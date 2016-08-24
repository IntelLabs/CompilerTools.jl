#=
Copyright (c) 2015, Intel Corporation
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
- Redistributions of source code must retain the above copyright notice,
  this list of conditions and the following disclaimer.
- Redistributions in binary form must reproduce the above copyright notice,
  this list of conditions and the following disclaimer in the documentation
  and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF
THE POSSIBILITY OF SUCH DAMAGE.
=#

module LivenessAnalysis

import ..DebugMsg
DebugMsg.init()

using CompilerTools
using CompilerTools.Helper
import CompilerTools.CFGs
using CompilerTools.LambdaHandling
using Core: Box, IntrinsicFunction

import Base.show

include("function-descriptions.jl")

export BlockLiveness, find_bb_for_statement, show

type Access
    sym
    read
end


"""
Liveness information for a TopLevelStatement in the CFG.
Contains a pointer to the corresponding CFG TopLevelStatement.
Contains def, use, live_in, and live_out for the current statement.
"""
type TopLevelStatement
    tls :: CFGs.TopLevelStatement

    def      :: Set{LHSVar}
    use      :: Set{LHSVar}
    live_in  :: Set{LHSVar}
    live_out :: Set{LHSVar}

    TopLevelStatement(t) = new(t, Set{LHSVar}(), Set{LHSVar}(), Set{LHSVar}(), Set{LHSVar}())
end

"""
Overload of Base.show to pretty-print a LivenessAnalysis.TopLevelStatement.
"""
function show(io::IO, tls::TopLevelStatement)
    print(io, "TLS ", tls.tls.index)

    print(io, " Def = (")
    for i in tls.def
      print(io, i, " ")
    end
    print(io, ") ")

    print(io, "Use = (")
    for i in tls.use
      print(io, i, " ")
    end
    print(io, ") ")

    print(io, "LiveIn = (")
    for i in tls.live_in
      print(io, i, " ")
    end
    print(io, ") ")

    print(io, "LiveOut = (")
    for i in tls.live_out
      print(io, i, " ")
    end
    print(io, ") ")

    println(io, "Expr: ", tls.tls.expr)
end

"""
Sometimes if new AST nodes are introduced then we need to ask for their def and use set as a whole
and then incorporate that into our liveness analysis directly.
"""
type AccessSummary
    def
    use
end

"""
Liveness information for a BasicBlock.
Contains a pointer to the corresponding CFG BasicBlock.
Contains def, use, live_in, and live_out for this basic block.
Contains an array of liveness information for the top level statements in this block.
"""
type BasicBlock
    cfgbb :: CFGs.BasicBlock

    def      :: Set{LHSVar}
    use      :: Set{LHSVar}
    live_in  :: Set{LHSVar}
    live_out :: Set{LHSVar}

    statements :: Array{TopLevelStatement,1}
 
    BasicBlock(bb) = new(bb, Set{LHSVar}(), Set{LHSVar}(), Set{LHSVar}(), Set{LHSVar}(), TopLevelStatement[])
end

"""
Overload of Base.show to pretty-print a LivenessAnalysis.BasicBlock.
"""
function show(io::IO, bb::BasicBlock)
    print(io, bb.cfgbb)
    print(io," Defs(")
    for j in bb.def
        print(io, " ", j)
    end
    print(io," ) Uses(")
    for j in bb.use
        print(io, " ", j)
    end
    print(io," ) LiveIn(")
    for j in bb.live_in
        print(io, " ", j)
    end
    print(io," ) LiveOut(")
    for j in bb.live_out
        print(io, " ", j)
    end
    println(io,")")

    tls = bb.statements
    if length(tls) == 0
        println(io,"Basic block without any statements.")
    end
    for j = 1:length(tls)
        if(DEBUG_LVL >= 5)
            print(io, "    ",tls[j].tls.index, "  ", tls[j].tls.expr)
            print(io,"  Defs(")
            for k in tls[j].def
                print(io, " ", k)
            end
            print(io," ) Uses(")
            for k in tls[j].use
                print(io, " ", k)
            end
            print(io," ) LiveIn(")
            for k in tls[j].live_in
                print(io, " ", k)
            end
            print(io," ) LiveOut(")
            for k in tls[j].live_out
                print(io, " ", k)
            end
            print(io," )")
            println(io)
        end
    end
end

"""
Called when AST traversal finds some Symbol or GenSym "sym" in a basic block "bb".
"read" is true if the symbol is being used and false if it is being defined.
"""
function add_access(bb, sym, read)
    @dprintln(3,"add_access ", sym, " ", read, " ", typeof(bb), " ")
    if bb == nothing    # If not in a basic block this is dead code so ignore.
        return nothing
    end

    assert(length(bb.statements) != 0)
    tls = bb.statements[end]    # Get the statement to which we will add access information.
    @dprintln(3, "tls = ", tls)
    write = !read

    # If this synbol is already in the statement then it is already in the basic block as a whole.
    # Therefore nothing would change if we did the rest of the function and we can shortcut quit here.
    if in(sym, tls.def)
        @dprintln(3, "sym already in tls.def")
        return nothing
    end

    # If the first use is a read then it goes in tls.use.
    # If there is a write after a read then it will be in tls.use and tls.def.
    # If there is a read after a write (which can happen for basic blocks) then we
    # ignore the read from the basic block perspective.

    # Handle access modifications at the statement level.
    if in(sym, tls.use)
        if write
            @dprintln(3, "sym already in tls.use so adding to def")
            # Handle write after read for a statement.
            push!(tls.def, sym)
        end
    elseif read
        if in(sym, tls.def)
            throw(string("Found a read after a write at the statement level in liveness analysis."))
        end
        @dprintln(3, "adding sym to tls.use ", sym)
        # Record the first use of this sym in this statement.
        push!(tls.use, sym)
    else # must be a write
        @dprintln(3, "adding sym to tls.def ", sym)
        # Record the first def of this sym in this statement.
        push!(tls.def, sym)
    end

    @dprintln(3, "tls after = ", tls)

    # Handle access modifications at the basic block level.
    if in(sym, bb.use)
        if write
            @dprintln(3, "sym already in bb.use so adding to def")
            # Handle write after read for a  basic block.
            push!(bb.def, sym)
        end
    elseif read
        if !in(sym, bb.def)
            @dprintln(3, "adding sym to bb.use ", sym)
            push!(bb.use, sym)
        end
    else # must be a write
        @dprintln(3, "adding sym to bb.def ", sym)
        push!(bb.def, sym)
    end

    @dprintln(4, "bb after = ", bb)

    nothing
end

"""
Holds the state during the AST traversal.
cfg = the control flow graph from the CFGs module.
map = our own map of CFG basic blocks to our own basic block information with liveness in it.
cur_bb = the current basic block in which we are processing AST nodes.
read = whether the sub-tree we are currently processing is being read or written.
ref_params = those arguments to the function that are passed by reference.
"""
type expr_state
    cfg :: CFGs.CFG
    map :: Dict{CFGs.BasicBlock, BasicBlock}
    cur_bb
    read
    ref_params :: Array{LHSVar, 1}
    params_not_modified :: Dict{Tuple{Any,Array{DataType,1}}, Array{Int64,1}} # Store function/signature mapping to an array whose entries corresponding to whether that argument passed to that function can be modified.
    params_not_modified_cb # a callback function to ask if some unknown function has unmodified args
    li :: Union{Void, LambdaVarInfo}

    function expr_state(cfg, no_mod, no_mod_cb)
        new(cfg, Dict{CFGs.BasicBlock, BasicBlock}(), nothing, true, LHSVar[], no_mod, no_mod_cb, nothing)
    end
end

"""
The main return type from LivenessAnalysis.
Contains a dictionary that maps CFG basic block to liveness basic blocks.
Also contains the corresponding CFG.
"""
type BlockLiveness
    basic_blocks :: Dict{CFGs.BasicBlock, BasicBlock}
    cfg :: CFGs.CFG

    function BlockLiveness(bb, cfg)
      new(bb, cfg)
    end
end

function getBasicBlockFromBlockNumber(block_num, bl :: BlockLiveness)
    cfg_bb = bl.cfg.basic_blocks[block_num]
    return bl.basic_blocks[cfg_bb]
end

"""
Helper function to say if the given LHSVar is in some basic block in "bl" for the given field (which is :def, :use, :live_in, or :live_out).
"""
function is_internal(x :: LHSVar, bl :: BlockLiveness, field)
    for entry in bl.basic_blocks
        if in(x, getfield(entry[2], field))
            return true
        end
    end
    
    return false
end

"""
Returns true if LHSVar x is part of the live_in field in some basic block in bl.
"""
function is_livein(x :: LHSVar, bl :: BlockLiveness)
    return is_internal(x, bl, :live_in)
end

"""
Returns true if LHSVar x is part of the live_out field in some basic block in bl.
"""
function is_liveout(x :: LHSVar, bl :: BlockLiveness)
    return is_internal(x, bl, :live_out)
end

"""
Returns true if LHSVar x is part of the def field in some basic block in bl.
"""
function is_def(x :: LHSVar, bl :: BlockLiveness)
    return is_internal(x, bl, :def)
end

"""
Returns true if LHSVar x is part of the use field in some basic block in bl.
"""
function is_use(x :: LHSVar, bl :: BlockLiveness)
    return is_internal(x, bl, :use)
end

"""
The live_in, live_out, def, and use routines are all effectively the same but just extract a different field name.
Here we extract this common behavior where x can be a liveness or CFG basic block or a liveness or CFG statement.
bl is BlockLiveness type as returned by a previous LivenessAnalysis.
field is the name of the field requested.
"""
function get_info_internal(x::Union{BasicBlock,TopLevelStatement}, bl::BlockLiveness, field)
    return getfield(x, field)
end

function get_info_internal(x::CFGs.BasicBlock, bl::BlockLiveness, field)
    bb = bl.basic_blocks[x]
    return getfield(bb, field)
end

function get_info_internal(x::CFGs.TopLevelStatement, bl::BlockLiveness, field)
    for i in bl.basic_blocks
        for j in i[2].statements
            if x == j.tls
                return getfield(j, field)
            end
        end
    end
    throw(string("Couldn't find liveness statement corresponding to cfg statement. "))
end

function get_info_internal(x::Any, bl::BlockLiveness, field)
    throw(string("get_info_internal called with non-BB and non-TopLevelStatement input."))
end

"""
Get the live_in information for "x" where x can be a liveness or CFG basic block or a liveness or CFG statement.
"""
function live_in(x, bl :: BlockLiveness)
    get_info_internal(x, bl, :live_in)
end

"""
Get the live_out information for "x" where x can be a liveness or CFG basic block or a liveness or CFG statement.
"""
function live_out(x, bl :: BlockLiveness)
    get_info_internal(x, bl, :live_out)
end

"""
Get the def information for "x" where x can be a liveness or CFG basic block or a liveness or CFG statement.
"""
function def(x, bl :: BlockLiveness)
    get_info_internal(x, bl, :def)
end

"""
Get the use information for "x" where x can be a liveness or CFG basic block or a liveness or CFG statement.
"""
function use(x, bl :: BlockLiveness)
    get_info_internal(x, bl, :use)
end

"""
Overload of Base.show to pretty-print BlockLiveness type.
"""
function show(io::IO, bl::BlockLiveness)
    println(io)
    body_order = CFGs.getBbBodyOrder(bl.cfg)
    for i = 1:length(body_order)
      cfgbb = bl.cfg.basic_blocks[body_order[i]]
      if !haskey(bl.basic_blocks, cfgbb)
        println(io,"Could not find LivenessAnalysis basic block for CFG basic block = ", cfgbb)
      else
        bb = bl.basic_blocks[bl.cfg.basic_blocks[body_order[i]]]
        show(io, bb)
        println(io)
      end
    end
end

"""
Query if the symbol in argument "x" is defined in live_info which can be a BasicBlock or TopLevelStatement.
"""
function isDef(x :: LHSVar, live_info)
  in(x, live_info.def)
end

"""
Search for a statement with the given top-level number in the liveness information.
Returns a LivenessAnalysis.TopLevelStatement having that top-level number or "nothing" if no such statement could be found.
"""
function find_top_number(top_number::Int, bl::BlockLiveness)
  # Liveness information stored in blocks so scan each block.
  for bb in bl.basic_blocks
    stmts = bb[2].statements
    # Scan each statement in this block for a matching statement number.
    for j = 1:length(stmts)
      if stmts[j].tls.index == top_number
        return stmts[j]
      end
    end
  end
  nothing
end


"""
Search for a basic block containing a statement with the given top-level number in the liveness information.
Returns a basic block label of a block having that top-level number or "nothing" if no such statement could be found.
"""
# Search for a statement with the given number in the liveness information.
function find_bb_for_statement(top_number::Int, bl::BlockLiveness)
  # Liveness information stored in blocks so scan each block.
  for bb in bl.basic_blocks
    stmts = bb[2].statements
    # Scan each statement in this block for a matching statement number.
    for j = 1:length(stmts)
      if stmts[j].tls.index == top_number
        return bb[1].label
      end
    end
  end

  @dprintln(3,"Didn't find statement top_number in basic_blocks.")
  nothing
end

"""
Clear the live_in and live_out data corresponding to all basic blocks and statements and then recompute liveness information.
"""
function recompute_live_ranges(state, dfn; array_params_live_out=true)
    for bb in state.basic_blocks
        empty!(bb.live_in)
        empty!(bb.live_out)
        for s in bb.statements
          empty!(s.live_in)
          empty!(s.live_out)
        end
    end

    compute_live_ranges(state, dfn, array_params_live_out)

    nothing
end

"""
Compute the live_in and live_out information for each basic block and statement.
"""
function compute_live_ranges(state :: expr_state, dfn, array_params_live_out)
    found_change = true
    bbs = state.cfg.basic_blocks

    # Compute the inter-block live ranges first.
    while found_change
        # Iterate until quiescence.
        found_change = false

        @dprintln(4, "Starting iteration of while loop in compute_live_ranges.")

        # For each basic block in reverse depth-first order.
        # This order optimizes the convergence time but isn't necessary for correctness.
        for i = length(dfn):-1:1
            bb_index = dfn[i]
            bb = state.map[bbs[bb_index]]   # get the basic block
            @dprintln(4, "Working on block ", bb_index)

            # add escaping variables to accum
            accum = state.li == nothing ? Set{LHSVar}() : Set{LHSVar}(getEscapingVariablesAsLHSVar(state.li))

            if bb_index == -2
              # Special case for final block.
              @dprintln(3,"Final block live_out = ", accum)
              # Nothing is live out of the final block.
              if array_params_live_out
                  accum = Set{LHSVar}(state.ref_params)
              end
            else
              # The live_out of any non-final block is the union of the live_in of every successor block.
              for j in bb.cfgbb.succs
                  @dprintln(4, bb_index, " adding from ", j.label, " live_in = ", state.map[j].live_in)
                  accum = union(accum, state.map[j].live_in)
              end
            end

            bb.live_out = accum
            @dprintln(4, bb_index, " bb.live_out = ", bb.live_out, " bb.use = ", bb.use, " bb.def = ", bb.def)

            old_size = length(bb.live_in)

            # The live_in to this block is the union of things used in this block 
            # with the set of things used by successors and not defined in this block.
            # Note that for basic blocks, we do not create a "use" if the first "use"
            # is after a "def".
            bb.live_in = union(bb.use, setdiff(bb.live_out, bb.def))
            @dprintln(4, bb_index, " bb.live_in = ", bb.live_in)

            new_size = length(bb.live_in)
            if new_size != old_size
                found_change = true
            end
        end
    end

    # Compute the intra-block live ranges using the inter-block live ranges.
    # For each basic block.
    for i = 1:length(dfn)
        bb = state.map[bbs[dfn[i]]]

        tls = bb.statements

        # The lives at the end of the last statement of this block is the inter-block live_out.
        cur_live_out = bb.live_out

        # Go through the statements in reverse order.
        for j = length(tls):-1:1
            tls[j].live_out = cur_live_out;
            tls[j].live_in  = union(tls[j].use, setdiff(tls[j].live_out, tls[j].def))
            cur_live_out    = tls[j].live_in
        end
    end

    nothing
end

"""
Dump a bunch of debugging information about BlockLiveness.
"""
function dump_bb(bl :: BlockLiveness)
    if DEBUG_LVL >= 4
      f = open("bbs.dot","w")
      println(f, "digraph bbs {")
    end

    body_order = CFGs.getBbBodyOrder(bl.cfg)
    if DEBUG_LVL >= 3
      println("body_order = ", body_order)
    end

    for i = 1:length(body_order)
        bb = bl.basic_blocks[bl.cfg.basic_blocks[body_order[i]]]
        @dprint(2,bb)

        if DEBUG_LVL >= 4
            for j in bb.cfgbb.succs
                println(f, bb.cfgbb.label, " -> ", j.label, ";")
            end
        end
    end

    if DEBUG_LVL >= 4
      println(f, "}")
      close(f)
    end
end

"""
Walk through an array of expressions.
Just recursively call from_expr for each expression in the array.
"""
function from_exprs(ast, depth :: Int64, state :: expr_state, callback :: Function, cbdata :: ANY)
    # sequence of expressions
    # ast = [ expr, ... ]
    local len = length(ast)
    for i = 1:len
      @dprintln(2,"Processing ast #",i," depth=",depth)
      @dprintln(3,"ast[", i, "] = ", ast[i])
      from_expr(ast[i], depth, state, callback, cbdata)
    end
    nothing
end

"""
Walk through an assignment expression.
"""
function from_assignment(ast :: Array{Any,1}, depth :: Int64, state :: expr_state, callback :: Function, cbdata :: ANY)
    # :(=) assignment
    # ast = [ ... ]
    assert(length(ast) == 2)
    local lhs = ast[1]
    local rhs = ast[2]
    @dprintln(3,"liveness from_assignment lhs = ", lhs, " rhs = ", rhs)
    # Process the right-hand side of the assignment unless it is a lambda.
    if isa(rhs, Expr) && rhs.head == :lambda
      # skip handling rhs lambdas
    else
      from_expr(rhs, depth, state, callback, cbdata)
    end
    @dprintln(3,"liveness from_assignment handling lhs")
    # Handle the left-hand side of the assignment which is being written.
    read_save = state.read
    state.read = false
    from_expr(lhs, depth, state, callback, cbdata)
    state.read = read_save
    @dprintln(3,"liveness from_assignment done handling lhs")
end

"""
Add an entry the dictionary of which arguments can be modified by which functions.
"""
function addUnmodifiedParams(func, signature :: Array{DataType,1}, unmodifieds, state :: expr_state)
    state.params_not_modified[(func, signature)] = unmodifieds
end

"""
Get the type of some AST node.
"""
function typeOfOpr(x::Expr, li :: LambdaVarInfo)
    @dprintln(3,"starting typeOfOpr, type = Expr")
    return typeOfOpr_fixType(x.typ)
end

function typeOfOpr(x::Symbol, li :: LambdaVarInfo)
    @dprintln(3,"starting typeOfOpr, type = LHSVar, x = ", x)
    return isLocalVariable(x, li) ? typeOfOpr_fixType(getType(x, li)) : Void
end

function typeOfOpr(x::RHSVar, li :: LambdaVarInfo)
    @dprintln(3,"starting typeOfOpr, x = ", x)
    typ1 = getType(toLHSVar(x), li)
    if isa(x, TypedVar) && x.typ != typ1
        @dprintln(2, "typeOfOpr x.typ and lambda type different")
        @dprintln(2, "x = ", x, " typ1 = ", typ1)
        @dprintln(2, "li = ", li)
        if (x.typ <: typ1) || is(typ1, Box) 
            typ1 = x.typ
        elseif (typ1 <: x.typ) || is(x.typ, Box) 
        else
            throw(string("typeOf Opr ", x, " is incompatible with its type in lambda ", typ1))
        end
    end
    assert(isa(typ1, Type))
    return typeOfOpr_fixType(typ1)
end

function typeOfOpr(x::GlobalRef, li :: LambdaVarInfo)
    @dprintln(3,"starting typeOfOpr, type = GlobalRef ", x)
    if x.name == :end
        return Int64
    else
        return typeOfOpr_fixType(typeof(eval(x)))
    end
end

function typeOfOpr(x::SimpleVector, li :: LambdaVarInfo)
    @dprintln(3,"starting typeOfOpr, type = SimpleVector")
    svec_types = [ typeOfOpr(x[i], li) for i = 1:length(x) ]
    return Tuple{svec_types...}
end

function typeOfOpr(x::Any, li :: LambdaVarInfo)
    @dprintln(3,"starting typeOfOpr, type = ",typeof(x))
    return typeOfOpr_fixType(typeof(x))
end

function typeOfOpr_fixType(ret::DataType)
    return ret
end

function typeOfOpr_fixType(ret::Union)
    return Tuple{ret.types...}
end

"""
Returns true if a parameter is passed by reference.
isbits types are not passed by ref but everything else is (is this always true..any exceptions?)
"""
function isPassedByRef(x, state :: expr_state)
    if isa(x, Tuple)
        return true
    elseif isbits(x)
        return false
    else
        return true
    end 
end

function showNoModDict(dict)
    for i in dict
      try
        @dprintln(4, "(", i[1][1], ",", i[1][2], ") => ", i[2])
      catch
        targs = i[1][2]
        assert(isa(targs, Tuple))
        println("EXCEPTION: type = ", typeof(targs))
        for j = 1:length(targs)
           println(j, " = ", typeof(targs[j]))
           println(targs[j])
        end
      end
    end
end

# If true, will assume that functions without "!" don't update their arguments.
use_inplace_naming_convention = false
function set_use_inplace_naming_convention()
    global use_inplace_naming_convention = true
end

wellknown_all_unmodified = Set{Any}()
wellknown_only_first_modified = Set{Any}()

function __init__()
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:(./)), force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:(.*)), force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:(.+)), force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:(.-)), force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:(/)),  force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:(*)),  force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:(+)),  force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:(-)),  force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:(<=)),  force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:(<)),  force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:(>=)),  force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:(>)),  force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:size), force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:maximum), force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:minimum), force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:max), force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:min), force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:mean), force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:ctranspose), force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base.LinAlg,:norm), force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:Ac_mul_B), force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:Ac_mul_Bc), force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:box), force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:arraylen), force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:arraysize), force = true))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base,:transpose), force = true))
#  push!(wellknown_all_unmodified, eval(TopNode(:(!))))
  push!(wellknown_all_unmodified, Base.resolve(GlobalRef(Base.LinAlg,:typeof), force = true))

    push!(wellknown_only_first_modified, Base.resolve(GlobalRef(Base.LinAlg,:gemm_wrapper!), force = true))
    push!(wellknown_only_first_modified, Base.resolve(GlobalRef(Base.LinAlg,:gemv!), force = true))
    push!(wellknown_only_first_modified, Base.resolve(GlobalRef(Base,:transpose!), force = true))
end

"""
For a given function and signature, return which parameters can be modified by the function.
If we have cached this information previously then return that, else cache the information for some
well-known functions or default to presuming that all arguments could be modified.
"""
function getUnmodifiedArgs(func :: ANY, args, arg_type_tuple :: Array{DataType,1}, state :: expr_state)
  @dprintln(3,"getUnmodifiedArgs func = ", func, " type = ", typeof(func))
  @dprintln(3,"getUnmodifiedArgs args = ", args)
  @dprintln(3,"getUnmodifiedArgs arg_type_tuple = ", arg_type_tuple)
  @dprintln(3,"getUnmodifiedArgs len(args) = ", length(arg_type_tuple))
  showNoModDict(state.params_not_modified)

  default_result = Int64[(isPassedByRef(x, state) ? 0 : 1) for x in arg_type_tuple]
  if length(default_result) == 0
    return default_result
  end

  if typeof(func) == GlobalRef
    func = Base.resolve(func, force=true)
    @dprintln(3,"getUnmodifiedArgs func = ", func, " type = ", typeof(func))
  elseif isTopNode(func)
    func = eval(func)
    @dprintln(3,"getUnmodifiedArgs func = ", func, " type = ", typeof(func))
  elseif typeof(func) == Expr
    return default_result
  end

  # We are seeing Symbol's getting here as well due to incomplete name resolution.  Once this is 
  # fixed then maybe we re-enable this assertion as a sanity check.
#  assert(typeof(func) == Function || typeof(func) == IntrinsicFunction)

  fs = (func, arg_type_tuple)
  if haskey(state.params_not_modified, fs)
    res = state.params_not_modified[fs]
    assert(length(res) == length(args))
    @dprintln(3,"function already in params_not_modified so returning previously computed value")
    return res
  end 

  for i in state.params_not_modified
    (f1, t1) = i[1]
    @dprintln(3,"f1 = ", f1, " t1 = ", t1, " f1type = ", typeof(f1), " len(t1) = ", length(t1))
    if func == f1 
      @dprintln(3,"function matches")
      if Tuple{arg_type_tuple...} <: Tuple{t1...}
        res = i[2]
        assert(length(res) == length(args))
        addUnmodifiedParams(func, arg_type_tuple, res, state)
        @dprintln(3,"exact match not found but sub-type match found")
        return res
      end
    end
  end

  if in(func, wellknown_all_unmodified)
    @dprintln(3,"Well-known function known not to modify args.")
    addUnmodifiedParams(func, arg_type_tuple, ones(Int64, length(args)), state) 
  elseif in(func, wellknown_only_first_modified)
    # only first argument is def
    local params_res = ones(Int64, length(args))
    params_res[1] = 0
    addUnmodifiedParams(func, arg_type_tuple, params_res, state)
  else
    if isBaseFunc(func, :tuple)
      @dprintln(3,"Detected tuple in getUnmodifiedArgs so returning that no arguments are modified.")
      addUnmodifiedParams(func, arg_type_tuple, [1 for x in arg_type_tuple], state)
      return state.params_not_modified[fs]
    end

    @dprintln(3,"is func generic => ", isa(func,Function))
    if use_inplace_naming_convention && isa(func,Function) && !in('!', string(Base.function_name(func)))
      @dprintln(3,"using naming convention that function has no ! so it doesn't modify anything in place.")
      addUnmodifiedParams(func, arg_type_tuple, [1 for x in arg_type_tuple], state)
    else
      if state.params_not_modified_cb != nothing && typeof(func) == GlobalRef
        res = state.params_not_modified_cb(func, arg_type_tuple)
        if res == nothing
          @dprintln(3,"fallback to args passed by ref as modified.")
          addUnmodifiedParams(func, arg_type_tuple, default_result, state)
        else
          @dprintln(3,"callback returned unmodified information.")
          addUnmodifiedParams(func, arg_type_tuple, res, state)
        end
      else
        @dprintln(3,"fallback to args passed by ref as modified.")
        addUnmodifiedParams(func, arg_type_tuple, default_result, state)
      end
    end
  end

  return state.params_not_modified[fs]
end

"""
Walk through a call expression.
"""
function from_call(ast :: Expr , depth :: Int64, state :: expr_state, callback :: Function, cbdata :: ANY)
  local fun  = getCallFunction(ast)
  local args = getCallArguments(ast)
  @dprintln(2,"from_call fun = ", fun, " typeof fun = ", typeof(fun), " args = ", args)
   
  # Form the signature of the call in an array.
  arg_type_array = DataType[]
  # For each argument to the call.
  for i = 1:length(args)
    @dprintln(3, "arg ", i, " = ", args[i], " typeof arg = ", typeof(args[i]))
    # Make sure the type of the argument resolves to a DataType.
    too = typeOfOpr(args[i], state.li)
    if !isa(too, DataType)
      @dprintln(0, "arg type = ", too, " tootype = ", typeof(too))
    end
    push!(arg_type_array, typeOfOpr(args[i], state.li)) 
  end
  @dprintln(3, "arg_type_array = ", arg_type_array)
  #arg_type_tuple = Tuple{arg_type_array...}
  # See which arguments to the function can be modified by the function.

  # We can do better/tighter analysis if we know which arguments to some call are modified.
  # bits type arguments are never modified.
  # non-bits types argument may be modified unless we know otherwise.
  # We prime a dictionary with some common, well-known functions and record that their non-bits type
  # arguments are not modified.
  # getUnmodifiedArgs returns an array to indicate which args to the call may be modified.
  unmodified_args = getUnmodifiedArgs(fun, args, arg_type_array, state)
  assert(length(unmodified_args) == length(args))
  @dprintln(3,"unmodified_args = ", unmodified_args)
  
  # symbols don't need to be translated
  if typeof(fun) != Symbol
      from_expr(fun, depth, state, callback, cbdata)
  end

  # For each argument.
  for i = 1:length(args)
    argtyp = typeOfOpr(args[i], state.li)
    @dprintln(2,"cur arg = ", args[i], " type = ", argtyp, " state.read = ", state.read)
    read_cache = state.read

    state.read = true
    # We can always potentially read first.
    from_expr(args[i], depth+1, state, callback, cbdata)
    if unmodified_args[i] == 0
      # The argument could be modified so treat it as a "def".
      state.read = false
      from_expr(args[i], depth+1, state, callback, cbdata)
#      state.read = true
    end
    state.read = read_cache
  end
end

"""
The default callback that processes no non-standard Julia AST nodes.
"""
function not_handled(a,b)
  nothing
end

"""
Count the number of times that the symbol in "s" is defined in all the basic blocks.
"""
function countSymbolDefs(s, lives)
  @dprintln(3,"countSymbolDefs: ", s)
  count = 0
  for (j,bb) in lives.basic_blocks
    @dprintln(3,"Examining block ", j.label)
    for stmt in bb.statements
      if in(s, stmt.def) 
          @dprintln(3, "Found symbol defined in block ", j.label, " in statement: ", stmt)
          count += 1 
      end
    end
  end
  return count
end

"""
ENTRY point to liveness analysis.
You must pass a lambda either as two parts, LambdaVarInfo and body, or as Expr (with :lambda head).
If you have non-standard AST nodes, you may pass a callback that will be given a chance to process the non-standard node first.
"""
function from_lambda(LambdaVarInfo :: LambdaVarInfo, body::ANY, callback=not_handled, cbdata :: ANY = nothing, no_mod=Dict{Tuple{Any,Array{DataType,1}}, Array{Int64,1}}(); no_mod_cb = nothing, array_params_live_out=true)
  if isa(body, Array)
    body = CompilerTools.LambdaHandling.getBody(body, getReturnType(LambdaVarInfo))
  end
  @assert (isa(body, Expr)) "Expect body to be Expr, but got " * string(typeof(body))
  #@dprintln(3,"liveness from_expr no_mod = ", no_mod)
  cfg = CFGs.from_lambda(body)      # Create the CFG from this lambda Expr.
  live_res = expr_state(cfg, no_mod, no_mod_cb)
  # Just to process the lambda and extract what the ref_params are.
  live_res.li = LambdaVarInfo
  live_res.ref_params = CompilerTools.LambdaHandling.getRefParams(live_res.li)
  # Process the body of the function via the CFG.
  res = fromCFG(live_res, cfg, callback, cbdata, array_params_live_out=array_params_live_out)
  input_params = CompilerTools.LambdaHandling.getInputParameters(live_res.li)
  ip_lhsvar = [CompilerTools.LambdaHandling.toLHSVar(x, live_res.li) for x in input_params]
  escape_lhsvar = CompilerTools.LambdaHandling.getEscapingVariablesAsLHSVar(live_res.li)
  start_live_in = getBasicBlockFromBlockNumber(CompilerTools.CFGs.CFG_ENTRY_BLOCK, res).live_in
  combined = union(ip_lhsvar, escape_lhsvar)
  use_before_init = setdiff(start_live_in, combined)
  @dprintln(2, "input_params = ", input_params)
  @dprintln(2, "ip_lhsvar = ", ip_lhsvar)
  @dprintln(2, "escape_lhsvar = ", escape_lhsvar)
  @dprintln(2, "combined = ", combined)
  @dprintln(2, "start_live_in = ", start_live_in)
  @dprintln(2, "use_before_init = ", use_before_init)
  if !isempty(use_before_init)
     @dprintln(1, "WARNING: use of variables before initialization = ", use_before_init)
     @dprintln(1, "LambdaVarInfo = ", live_res.li)
#     throw(string("WARNING: use of variables before initialization = ", use_before_init))
  end
  res
end

function from_lambda(lambda::Union{Expr,LambdaInfo}, callback=not_handled, cbdata :: ANY = nothing, no_mod=Dict{Tuple{Any,Array{DataType,1}}, Array{Int64,1}}(); no_mod_cb = nothing, array_params_live_out=true)
    linfo, body = CompilerTools.LambdaHandling.lambdaToLambdaVarInfo(lambda)
    from_lambda(linfo, body, callback, cbdata, no_mod; no_mod_cb = no_mod_cb, array_params_live_out = array_params_live_out)
end

"""
Extract liveness information from the CFG.
"""
function fromCFG(live_res, cfg :: CFGs.CFG, callback :: Function, cbdata :: ANY; array_params_live_out=true)
  @dprintln(2,"fromCFG")
  CFGs.dump_bb(cfg)   # Dump debugging information if set_debug_level is high enough.

  # For each basic block.
  for bb in cfg.basic_blocks
    live_res.map[bb[2]] = BasicBlock(bb[2])
    live_res.cur_bb = live_res.map[bb[2]]

    @dprintln(4,"fromCFG cur_bb = ", live_res.cur_bb)
    # For each statement in each block.
    for i = 1:length(bb[2].statements)
       cur_stmt = bb[2].statements[i]
       # Add this statement to our list of statements in the current LivenessAnalysis.BasicBlock.
       push!(live_res.cur_bb.statements, TopLevelStatement(cur_stmt)) 
       @dprintln(3,"fromCFG stmt = ", cur_stmt.expr)
       # Process the statement looking for def and use.
       from_expr(cur_stmt.expr, 1, live_res, callback, cbdata)
    end
  end

  @dprintln(4,"fromCFG live_res before live ranges = ", live_res)
  # Compute live_in and live_out for basic blocks and statements.
  compute_live_ranges(live_res, cfg.depth_first_numbering, array_params_live_out)
  @dprintln(2,"Dumping basic block info from_expr.")
  ret = BlockLiveness(live_res.map, cfg)
  dump_bb(ret)
  return ret
end

"""
Process a return Expr node which is just a recursive processing of all of its args.
"""
function from_return(args, depth :: Int64, state :: expr_state, callback :: Function, cbdata :: ANY)
    @dprintln(2,"Expr return: ")
    from_exprs(args, depth, state, callback, cbdata)
    nothing
end

"""
Process a gotoifnot which is just a recursive processing of its first arg which is the conditional.
"""
function from_if(args, depth :: Int64, state :: expr_state, callback :: Function, cbdata :: ANY)
    # The structure of the if node is an array of length 2.
    assert(length(args) == 2)
    # The first index is the conditional.
    if_clause  = args[1]

    # Process the conditional as part of the current basic block.
    from_expr(if_clause, depth, state, callback, cbdata)
    nothing
end

"""
Generic routine for how to walk most AST node types.
"""
function from_expr(ast::LambdaInfo,
                   depth::Int64,
                   state::expr_state,
                   callback::Function,
                   cbdata::ANY)
    # skip processing LambdaInfo
    @dprintln(3, "LivenessAnalysis: skip processing nested LambdaInfo")
    return nothing
end

function from_expr(ast::ANY,
                   depth::Int64,
                   state::expr_state,
                   callback::Function,
                   cbdata::ANY)
    @dprintln(2,"from_expr ast = ", ast, " depth = ",depth," ", " asttyp = ", typeof(ast), " state.read = ", state.read)

    handled = callback(ast, cbdata)
    @dprintln(3,"callback handled ", handled)
    if handled != nothing
        if length(handled) > 0
            @dprintln(3,"Processing expression from callback for ", ast)
            @dprintln(3,handled)
            from_exprs(handled, depth+1, state, callback, cbdata)
            @dprintln(3,"Done processing expression from callback.")
        end
        return nothing
    end

    from_expr_helper(ast, depth, state, callback, cbdata)
end

function from_expr_helper(ast::Tuple,
                          depth::Int64,
                          state::expr_state,
                          callback::Function,
                          cbdata::ANY)
    # N.B. This also handles the empty tuple correctly.

    for i = 1:length(ast)
        from_expr(ast[i], depth, state, callback, cbdata)
    end
end

function from_expr_helper(ast::Expr,
                          depth::Int64,
                          state::expr_state,
                          callback::Function,
                          cbdata::ANY)
    # If you have an assignment with an Expr as its left-hand side then you get here with "read = false"
    # but that doesn't  mean the whole Expr is written.  In fact, none of it is written so we set read
    # back to true and then restore in the incoming read value at the end.
    read_save  = state.read
    state.read = true

    @dprint(2,"Expr ")
    local head = ast.head
    local args = ast.args
    local typ  = ast.typ
    @dprintln(2,head, " ", args)
    if head == :lambda
        # from_lambda(ast, depth, state, callback, cbdata)
        @dprintln(0, "nested :lambda skipped")
    elseif head == :body
        @dprintln(0,":body found in from_expr")
        throw(string(":body found in from_expr"))
    elseif head == :(=)
        from_assignment(args, depth, state, callback, cbdata)
    elseif head == :return
        from_return(args, depth, state, callback, cbdata)
    elseif head == :invoke || head == :call || head == :call1
        from_call(ast, depth, state, callback, cbdata)
        # TODO: catch domain IR result here
        # TODO?: tuple
    elseif head == :gotoifnot
        from_if(args,depth,state, callback, cbdata)
    elseif head == :line || head == :inbounds || head == :boundscheck || head == :meta || head == :type_goto || head == :static_parameter
        # Intentionally do nothing.
    elseif head == :copyast
        @dprintln(2,"copyast type")
        # Intentionally do nothing.
    elseif head == :alloc
        from_exprs(args[2], depth+1, state, callback, cbdata)
    elseif head == :assert || head == :select || head == :ranges || head == :range || head == :static_typeof ||
        head == :tomask || head == :arraysize || head == :copy || head == :new ||
        head == :tuple || head == :getindex || head == :quote || head == Symbol("'") ||
        head == :(&) || head == :(~) || head == :(|) || head == :($) || head == :(>>>) || head == :(>>) || head == :(<<)
        from_exprs(args, depth+1, state, callback, cbdata)
    elseif head == :(.)
        # skip handling fields of a type
        # ISSUE: will this cause precision issue, or correctness issue? I guess it is precision?
    else
        throw(string("from_expr: unknown Expr head :", head))
    end
    state.read = read_save
end

function from_expr_helper(ast::LabelNode,
                          depth::Int64,
                          state::expr_state,
                          callback::Function,
                          cbdata::ANY)
    assert(false)
    # from_label(ast.label, state, callback, cbdata)
end

function from_expr_helper(ast::Union{GotoNode,LineNumberNode,TopNode,Module},
                          depth::Int64,
                          state::expr_state,
                          callback::Function,
                          cbdata::ANY)
    # Intentionally do nothing.
end

function from_expr_helper(ast::Union{Symbol,RHSVar},
                          depth::Int64,
                          state::expr_state,
                          callback::Function,
                          cbdata::ANY)
    # addStatement(top_level, state, ast)
    @dprintln(2, "ast = ", ast, "::", typeof(ast))
    if isVariableDefined(ast, state.li)
        v = toLHSVar(ast, state.li)
        add_access(state.cur_bb, v, state.read)
    end
end

function from_expr_helper(ast::Union{DataType,AbstractString,NewvarNode,Void},
                          depth::Int64,
                          state::expr_state,
                          callback::Function,
                          cbdata::ANY)
    # addStatement(top_level, state, ast)
end

function from_expr_helper(ast::QuoteNode,
                          depth::Int64,
                          state::expr_state,
                          callback::Function,
                          cbdata::ANY)
    # addStatement(top_level, state, ast)
    local value = ast.value
    #TODO: fields: value
    @dprintln(3,"QuoteNode type ",typeof(value))
end

function from_expr_helper(ast::AccessSummary,
                          depth::Int64,
                          state::expr_state,
                          callback::Function,
                          cbdata::ANY)
    @dprintln(3, "Incorporating AccessSummary")
    for i in ast.use
        add_access(state.cur_bb, i, true)
    end
    for i in ast.def
        add_access(state.cur_bb, i, false)
    end  
end

function from_expr_helper(ast::ANY,
                          depth::Int64,
                          state::expr_state,
                          callback::Function,
                          cbdata::ANY)
    asttyp = typeof(ast)

    if isdefined(:GetfieldNode) && asttyp == GetfieldNode  # GetfieldNode = value + name
        # addStatement(top_level, state, ast)
        @dprintln(3,"GetfieldNode type ",typeof(ast.value), " ", ast)
    elseif isdefined(:GlobalRef) && asttyp == GlobalRef
        # addStatement(top_level, state, ast)
        @dprintln(3,"GlobalRef type ",typeof(ast.mod), " ", ast)  # GlobalRef = mod + name
    elseif isbits(asttyp)
        # addStatement(top_level, state, ast)
        # skip
    elseif asttyp.name == Array.name
        # addStatement(top_level, state, ast)
        @dprintln(3,"Handling case of AST node that is an array. ast = ", ast, " typeof(ast) = ", asttyp)
        for i = 1:length(ast)
            from_expr(ast[i], depth, state, callback, cbdata)
        end
    elseif asttyp == Symbol
        # skip
    else
        throw(string("from_expr: unknown AST type :", asttyp, " ", ast))
    end
end

end
