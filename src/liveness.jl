module LivenessAnalysis

using CompilerTools.AstWalker
using CompilerTools.CFGs

import Base.show

# This controls the debug print level.  0 prints nothing.  At the moment, 2 prints everything.
DEBUG_LVL=0

function set_debug_level(x)
    global DEBUG_LVL = x
end

# A debug print routine.
function dprint(level,msgs...)
    if(DEBUG_LVL >= level)
        print(msgs...)
    end
end

# A debug print routine.
function dprintln(level,msgs...)
    if(DEBUG_LVL >= level)
        println(msgs...)
    end
end

function TypedExpr(typ, rest...)
    res = Expr(rest...)
    res.typ = typ
    res
end

export from_exprs, set_debug_level, BlockLiveness, find_bb_for_statement, show

type Access
    sym
    read
end

type TopLevelStatement
    tls :: CFGs.TopLevelStatement

    def
    use
    live_in
    live_out

    TopLevelStatement(t) = new(t, Set(), Set(), Set(), Set())
end

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

type AccessSummary
    def
    use
end

type BasicBlock
    cfgbb :: CFGs.BasicBlock
    def
    use
    live_in
    live_out
    statements :: Array{TopLevelStatement,1}
 
    BasicBlock(bb) = new(bb, Set(),Set(), Set(), Set(), TopLevelStatement[])
end

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

    tls = bb.statements
    if length(tls) == 0
        println(io,"Basic block without any statements.")
    end
    for j = 1:length(tls)
        print(io, "    ",tls[j].tls.index, "  ", tls[j].tls.expr)
        if(DEBUG_LVL >= 5)
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
        end
        println(io)
    end
end

import Base.show

function add_access(bb, sym, read)
    dprintln(3,"add_access ", sym, " ", read, " ", typeof(bb), " ")
    if bb == nothing
        return nothing
    end

    assert(length(bb.statements) != 0)
    tls = bb.statements[end]
    dprintln(3, "tls = ", tls)
    write = !read

    # If this synbol is already in a statement then it is already in the basic block as a whole.
    if in(sym, tls.def)
        dprintln(3, "sym already in tls.def")
        return nothing
    end

    # If the first use is a read then it goes in tls.use.
    # If there is a write after a read then it will be in tls.use and tls.def.
    # If there is a read after a write (which can happen for basic blocks) then we
    # ignore the read from the basic block perspective.
    if in(sym, tls.use)
        if write
            dprintln(3, "sym already in tls.use so adding to def")
            push!(tls.def, sym)
        end
    elseif read
        if in(sym, tls.def)
            throw(string("Found a read after a write at the statement level in liveness analysis."))
        end
        dprintln(3, "adding sym to tls.use")
        push!(tls.use, sym)
    else # must be a write
        dprintln(3, "adding sym to tls.def")
        push!(tls.def, sym)
    end

    if in(sym, bb.use)
        if write
            dprintln(3, "sym already in bb.use so adding to def")
            push!(bb.def, sym)
        end
    elseif read
        if !in(sym, bb.def)
            dprintln(3, "adding sym to bb.use")
            push!(bb.use, sym)
        end
    else # must be a write
        dprintln(3, "adding sym to bb.def")
        push!(bb.def, sym)
    end

    nothing
end

type expr_state
    cfg :: CFGs.CFG
    map :: Dict{CFGs.BasicBlock, BasicBlock}
    cur_bb
    read
    ref_params :: Array{Symbol, 1}

    function expr_state(cfg)
        new(cfg, Dict{CFGs.BasicBlock, BasicBlock}(), nothing, true, Symbol[])
    end
end

type BlockLiveness
    basic_blocks :: Dict{CFGs.BasicBlock, BasicBlock}
    cfg :: CFGs.CFG

    function BlockLiveness(bb, cfg)
      new(bb, cfg)
    end
end

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

function isDef(x, live_info)
  in(x,live_info.def)
end

# Search for a statement with the given number in the liveness information.
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
#  throw(string("find_top_number: could not find top_number :", top_number))
end


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

  dprintln(3,"Didn't find statement top_number in basic_blocks.")

#  for bb in bl.basic_blocks
#    stmts = bb[2].statements
#    for j = 1:length(stmts)
#      dprintln(3,stmts[j])
#    end
#  end

#  throw(string("find_bb_for_statement: could not find top_number :", top_number))
  nothing
end

function recompute_live_ranges(state, dfn)
    for bb in state.basic_blocks
        empty!(bb.live_in)
        empty!(bb.live_out)
        for s in bb.statements
          empty!(s.live_in)
          empty!(s.live_out)
        end
    end

    compute_live_ranges(state, dfn)

    nothing
end

function compute_live_ranges(state, dfn)
    found_change = true
    bbs = state.cfg.basic_blocks

    # Compute the inter-block live ranges.
    while found_change
        found_change = false

        for i = length(dfn):-1:1
            bb_index = dfn[i]
            bb = state.map[bbs[bb_index]]

            accum = Set()
            if bb_index == -2
              # Special case for final block.
              # Treat input arrays as live at end of function.
              accum = Set{Symbol}(state.ref_params)
              dprintln(3,"Final block live_out = ", accum)
            else
              for j in bb.cfgbb.succs
                accum = union(accum, state.map[j].live_in)
              end
            end

            bb.live_out = accum

            old_size = length(bb.live_in)

            bb.live_in = union(bb.use, setdiff(bb.live_out, bb.def))

            new_size = length(bb.live_in)
            if new_size != old_size
                found_change = true
            end
        end

    end

    # Compute the intra-block live ranges.
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
        dprint(2,bb)

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

uncompressed_ast(l::LambdaStaticData) =
  isa(l.ast,Expr) ? l.ast : ccall(:jl_uncompress_ast, Any, (Any,Any), l, l.ast)

function get_ref_params(input_vars, var_types)
  ret = Symbol[]
        
  dprintln(3,"input_vars = ", input_vars)
  dprintln(3,"var_types = ", var_types)
    
  for i = 1:length(input_vars)
    iv = input_vars[i]
    dprintln(3,"iv = ", iv, " type = ", typeof(iv))
    found = false
    for j = 1:length(var_types)
      dprintln(3,"vt = ", var_types[j][1], " type = ", typeof(var_types[j][1]))
      if iv == var_types[j][1]
        dprintln(3,"Found matching name.")
        #if var_types[j][2].name == Array.name
        #  dprintln(3,"Parameter is an Array.")
        if !isbits(var_types[j][2])
          dprintln(3,"Parameter is not a bits type.")
          push!(ret, iv)
        end
        found = true
        break
      end
    end
    if !found
      throw(string("Didn't find parameter variable in type list."))
    end
  end

  ret
end

# :lambda expression
# ast = [ parameters, meta (local, types, etc), body ]
function from_lambda(ast::Array{Any,1}, depth, state, callback, cbdata)
  assert(length(ast) == 3)
  local param = ast[1]
  local meta  = ast[2]
  local body  = ast[3]
  dprintln(3,"param = ", param)
  dprintln(3,"meta  = ", meta)
  state.ref_params = get_ref_params(param, meta[2])
  dprintln(3,"from_lambda: ref_params = ", state.ref_params)
end

# sequence of expressions
# ast = [ expr, ... ]
function from_exprs(ast::Array{Any,1}, depth, state, callback, cbdata)
  local len = length(ast)
  for i = 1:len
    dprintln(2,"Processing ast #",i," depth=",depth)
    dprintln(3,"ast[", i, "] = ", ast[i])
    from_expr(ast[i], depth, state, callback, cbdata)
  end
  nothing
end

# :(=) assignment
# ast = [ ... ]
function from_assignment(ast::Array{Any,1}, depth, state, callback, cbdata)
  assert(length(ast) == 2)
  local lhs = ast[1]
  local rhs = ast[2]
  dprintln(3,"liveness from_assignment lhs = ", lhs, " rhs = ", rhs)
  if isa(rhs, Expr) && rhs.head == :lambda
    # skip handling rhs lambdas
  else
    from_expr(rhs, depth, state, callback, cbdata)
  end
  dprintln(3,"liveness from_assignment handling lhs")
  state.read = false
  from_expr(lhs, depth, state, callback, cbdata)
  state.read = true
  dprintln(3,"liveness from_assignment done handling lhs")
end

params_not_modified = Dict{Any, Array{Int32,1}}()
function addUnmodifiedParams(func, signature, unmodifieds)
  params_not_modified[(func, signature)] = unmodifieds
end

function getUnmodifiedArgs(func, args, arg_type_tuple, params_not_modified)
  fs = (func, arg_type_tuple)
  if haskey(params_not_modified, fs)
    res = params_not_modified[fs]
    assert(length(res) == length(args))
    return res
  end 

  if func == :(./) || func == :(.*) || func == :(.+) || func == :(.-) ||
     func == :(/)  || func == :(*)  || func == :(+)  || func == :(-)
    addUnmodifiedParams(func, arg_type_tuple, ones(Int32, length(args))) 
  elseif func == :SpMV
    addUnmodifiedParams(func, arg_type_tuple, [1,1]) 
  else
    addUnmodifiedParams(func, arg_type_tuple, zeros(Int32, length(args))) 
  end

  return params_not_modified[fs]
end

function from_call(ast::Array{Any,1}, depth, state, callback, cbdata)
  assert(length(ast) >= 1)
  local fun  = ast[1]
  local args = ast[2:end]
  dprintln(2,"from_call fun = ", fun, " typeof fun = ", typeof(fun))
  if length(args) > 0
    dprintln(2,"first arg = ",args[1], " type = ", typeof(args[1]))
  end
   
  texpr = Expr(:tuple)
  for i = 1:length(args)
    argtyp = typeof(args[i])
    push!(texpr.args, argtyp) 
  end
  arg_type_tuple = eval(texpr)
  unmodified_args = getUnmodifiedArgs(fun, args, arg_type_tuple, params_not_modified)
  assert(length(unmodified_args) == length(args))
  
  # symbols don't need to be translated
  if typeof(fun) != Symbol
      from_expr(fun, depth, state, callback, cbdata)
  end

  for i = 1:length(args)
    argtyp = typeof(args[i])
    dprintln(2,"cur arg = ", args[i], " type = ", argtyp)

    if(argtyp == Symbol)
      from_expr(args[i], depth+1, state, callback, cbdata)
    elseif argtyp == SymbolNode
      if isbits(args[i].typ)
        from_expr(args[i], depth+1, state, callback, cbdata)
      else
        from_expr(args[i], depth+1, state, callback, cbdata)
        if unmodified_args[i] == 1
          from_expr(args[i], depth+1, state, callback, cbdata)
        else
          state.read = false
          from_expr(args[i], depth+1, state, callback, cbdata)
          state.read = true
        end
      end
    else
      from_expr(args[i], depth+1, state, callback, cbdata)
    end
  end
end

function not_handled(a,b)
  nothing
end

function countSymbolDefs(s, lives)
  count = 0
  for (j,bb) in lives.basic_blocks
    for stmt in bb.statements
      if in(s, stmt.def) count += 1 end
    end
  end
  return count
end

# ENTRY
function from_expr(ast::Any, callback=not_handled, cbdata=nothing)
  assert(typeof(ast) == Expr)
  assert(ast.head == :lambda)
  cfg = CFGs.from_ast(ast)
  live_res = expr_state(cfg)
  # Just to process the lambda.
  from_expr(ast, 1, live_res, callback, cbdata)
  fromCFG(live_res, cfg, callback, cbdata)
end

function fromCFG(live_res, cfg :: CFGs.CFG, callback, cbdata)
  dprintln(2,"fromCFG")
  CFGs.dump_bb(cfg)

  for bb in cfg.basic_blocks
    live_res.map[bb[2]] = BasicBlock(bb[2])
    live_res.cur_bb = live_res.map[bb[2]]

    for i = 1:length(bb[2].statements)
       cur_stmt = bb[2].statements[i]
       push!(live_res.cur_bb.statements, TopLevelStatement(cur_stmt)) 
       dprintln(3,"fromCFG stmt = ", cur_stmt.expr)
       from_expr(cur_stmt.expr, 1, live_res, callback, cbdata)
    end
  end

  compute_live_ranges(live_res, cfg.depth_first_numbering)
  dprintln(2,"Dumping basic block info from_expr.")
  ret = BlockLiveness(live_res.map, cfg)
  dump_bb(ret)
  return ret
end

function from_return(args, depth, state, callback, cbdata)
    dprintln(2,"Expr return: ")
    from_exprs(args, depth, state, callback, cbdata)
    nothing
end

function from_if(args, depth, state, callback, cbdata)
    # The structure of the if node is an array of length 2.
    assert(length(args) == 2)
    # The first index is the conditional.
    if_clause  = args[1]

    # Process the conditional as part of the current basic block.
    from_expr(if_clause, depth, state, callback, cbdata)
    nothing
end

function from_expr(ast::Any, depth, state, callback, cbdata)
  if typeof(ast) == LambdaStaticData
      # ast = uncompressed_ast(ast)
      # skip processing LambdaStaticData
      return nothing
  end
  local asttyp = typeof(ast)
  dprintln(2,"from_expr depth=",depth," ", " asttyp = ", asttyp)

  handled = callback(ast, cbdata)
  if handled != nothing
#    addStatement(top_level, state, ast)
    if length(handled) > 0
      dprintln(3,"Processing expression from callback for ", ast)
      dprintln(3,handled)
      from_exprs(handled, depth+1, state, callback, cbdata)
      dprintln(3,"Done processing expression from callback.")
    end
    return nothing
  end

  if isa(ast, Tuple)
    for i = 1:length(ast)
        from_expr(ast[i], depth, state, callback, cbdata)
    end
  elseif asttyp == Expr
    #addStatement(top_level, state, ast)

    dprint(2,"Expr ")
    local head = ast.head
    local args = ast.args
    local typ  = ast.typ
    dprintln(2,head, " ", args)
    if head == :lambda
        from_lambda(args, depth, state, callback, cbdata)
    elseif head == :body
        dprintln(0,":body found in from_expr")
        throw(string(":body found in from_expr"))
    elseif head == :(=)
        from_assignment(args,depth,state, callback, cbdata)
    elseif head == :return
        from_return(args,depth,state, callback, cbdata)
    elseif head == :call
        from_call(args,depth,state, callback, cbdata)
        # TODO: catch domain IR result here
    elseif head == :call1
        from_call(args,depth,state, callback, cbdata)
        # TODO?: tuple
    elseif head == :line
        # skip
    elseif head == :arraysize
        from_exprs(args, depth+1, state, callback, cbdata)
        # skip
    elseif head == :alloc
        from_exprs(args[2], depth+1, state, callback, cbdata)
        # skip
    elseif head == :copy
        from_exprs(args, depth+1, state, callback, cbdata)
        # skip
    elseif head == :assert || head == :select || head == :ranges || head == :range || head == :tomask
        from_exprs(args, depth+1, state, callback, cbdata)
    elseif head == :copyast
        dprintln(2,"copyast type")
        # skip
#    elseif head == :assertEqShape
        #addStatement(top_level, state, ast)
#        assert(length(args) == 2)
        #dprintln(3,"liveness: assertEqShape ", args[1], " ", args[2], " ", typeof(args[1]), " ", typeof(args[2]))
#        add_access(state.cur_bb, args[1].name, state.read)
#        add_access(state.cur_bb, args[2].name, state.read)
    elseif head == :gotoifnot
        from_if(args,depth,state, callback, cbdata)
    elseif head == :new
        from_exprs(args, depth+1, state, callback, cbdata)
    elseif head == :tuple
        from_exprs(args, depth+1, state, callback, cbdata)
    elseif head == :getindex
        from_exprs(args, depth+1, state, callback, cbdata)
    elseif head == :boundscheck
    elseif head == :(.)
        # skip handling fields of a type
        # ISSUE: will this cause precision issue, or correctness issue? I guess it is precision?
    elseif head == :quote
        from_exprs(args, depth+1, state, callback, cbdata)
    else
        throw(string("from_expr: unknown Expr head :", head))
    end
  elseif asttyp == LabelNode
    assert(false)
#    from_label(ast.label, state, callback, cbdata)
  elseif asttyp == GotoNode
#    addStatement(top_level, state, ast)
#    from_goto(ast.label, state, callback, cbdata)
#     assert(false)
#    INTENTIONALLY DO NOTHING
  elseif asttyp == Symbol
    #addStatement(top_level, state, ast)
    dprintln(2,"Symbol type ", ast)
    add_access(state.cur_bb, ast, state.read)
  elseif asttyp == LineNumberNode
    #skip
  elseif asttyp == SymbolNode # name, typ
    #addStatement(top_level, state, ast)
    dprintln(2,"SymbolNode type ", ast.name, " ", ast.typ)
    add_access(state.cur_bb, ast.name, state.read)
  elseif asttyp == TopNode    # name
    #skip
  elseif isdefined(:GetfieldNode) && asttyp == GetfieldNode  # GetfieldNode = value + name
    #addStatement(top_level, state, ast)
    dprintln(3,"GetfieldNode type ",typeof(ast.value), " ", ast)
  elseif isdefined(:GlobalRef) && asttyp == GlobalRef
    #addStatement(top_level, state, ast)
    dprintln(3,"GlobalRef type ",typeof(ast.mod), " ", ast)  # GlobalRef = mod + name
  elseif asttyp == QuoteNode
    #addStatement(top_level, state, ast)
    local value = ast.value
    #TODO: fields: value
    dprintln(3,"QuoteNode type ",typeof(value))
  # elseif asttyp == Int64 || asttyp == Int32 || asttyp == Float64 || asttyp == Float32
  elseif isbits(asttyp)
    #addStatement(top_level, state, ast)
    #skip
  elseif asttyp.name == Array.name
    #addStatement(top_level, state, ast)
    dprintln(3,"Handling case of AST node that is an array. ast = ", ast, " typeof(ast) = ", asttyp)
    for i = 1:length(ast)
      from_expr(ast[i], depth, state, false, callback, cbdata)
    end
  elseif asttyp == DataType
    #addStatement(top_level, state, ast)
  elseif asttyp == ()
    #addStatement(top_level, state, ast)
  elseif asttyp == ASCIIString
    #addStatement(top_level, state, ast)
  elseif asttyp == NewvarNode
    #addStatement(top_level, state, ast)
  elseif asttyp == Nothing
    #addStatement(top_level, state, ast)
  elseif asttyp == AccessSummary
    dprintln(3, "Incorporating AccessSummary")
    for i in ast.use
      add_access(state.cur_bb, i, true)
    end
    for i in ast.def
      add_access(state.cur_bb, i, false)
    end  
  elseif asttyp == Module
    #skip
  else
    throw(string("from_expr: unknown AST type :", asttyp, " ", ast))
  end
  nothing
end

end

