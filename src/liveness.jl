module LivenessAnalysis

using CompilerTools.AstWalker

import Base.show

# This controls the debug print level.  0 prints nothing.  At the moment, 2 prints everything.
DEBUG_LVL=0

#if !isdefined(:GetfieldNode)
#    typealias GetfieldNode GlobalRef
#end

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

export from_exprs, set_debug_level, BlockLiveness, DomLoops, Loop, find_bb_for_statement

type Access
    sym
    read
end

type TopLevelStatement
    index
    def
    use
    live_in
    live_out
    expr

    TopLevelStatement(i, ex) = new(i,Set(),Set(),Set(),Set(), ex)
end

type AccessSummary
    def
    use
end

type BasicBlock
    label
    def
    use
    preds :: Set{BasicBlock}
    succs :: Set{BasicBlock}
    fallthrough_succ
    live_in
    live_out
    depth_first_number
    statements :: Array{TopLevelStatement,1}
 
    BasicBlock(label) = new(label,Set(),Set(),Set{BasicBlock}(),Set{BasicBlock}(),nothing,Set(),Set(),nothing,TopLevelStatement[])
end

function addStatement(top_level, state, ast)
    dprintln(3, "addStatement ", ast, " ", top_level, " ", state.cur_bb == nothing)
    if top_level && state.cur_bb != nothing
        dprintln(3,"liveness adding statement number ", state.top_level_number)
        for i in state.cur_bb.statements
          if i.index == state.top_level_number
            throw(string("statement number already there"))
          end
        end
        push!(state.cur_bb.statements,TopLevelStatement(state.top_level_number, ast))
        return true
    end
    return false
end

function show(io::IO, bb::BasicBlock)
    print(io, "BasicBlock ", bb.label, ": Pred(")
    for j in bb.preds
        print(io," ",j.label)
    end
    print(io," ) Succ(")
    for j in bb.succs
        print(io," ",j.label)
    end
    print(io," ) fallthrough = ", bb.fallthrough_succ == nothing ? "nothing" : bb.fallthrough_succ.label, " Defs(")
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

    if bb.depth_first_number != nothing
        println(io, " ) depth_first=", bb.depth_first_number)
    else
        println(io, " )")
    end

    tls = bb.statements
    if length(tls) == 0
        println(io,"Basic block without any statements.")
    end
    for j = 1:length(tls)
        print(io, "    ",tls[j].index, "  ", tls[j].expr)
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

function add_access(bb, sym, read, top_level_index)
    dprintln(3,"add_access ", sym, " ", read, " ", typeof(bb), " ", top_level_index)
    if bb == nothing
        return nothing
    end

    assert(length(bb.statements) != 0)
    if bb.statements[end].index != top_level_index
      dprintln(0,bb.statements[end])
      assert(bb.statements[end].index == top_level_index)
    end

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

if false
    if in(sym, tls.use)
        if !read
            dprintln(3, "sym already in tls.use so adding to def")
            push!(tls.def, sym)
        end

        dprintln(3, "sym already in tls.use")
        return nothing
    end

    if read
        dprintln(3, "adding sym to tls.use")
        push!(tls.use, sym)
    else
        dprintln(3, "adding sym to tls.def")
        push!(tls.def, sym)
    end

    if in(sym, bb.def) || in(sym, bb.use)
        return nothing
    end

    if read
        push!(bb.use, sym)
    else
        push!(bb.def, sym)
    end
end

    nothing
end

function connect(from, to, fallthrough)
    if from != nothing
        push!(from.succs,to)
        push!(to.preds,from)
        if fallthrough
          from.fallthrough_succ = to
        end
    end
end

type expr_state
    basic_blocks :: Dict{Int,BasicBlock}
    cur_bb
    next_if :: Int
    read
    top_level_number :: Int
    ref_params :: Array{Symbol, 1}

    function expr_state()
        start  = BasicBlock(-1)
        finish = BasicBlock(-2)
        init   = Dict{Any,BasicBlock}
        bbs = Dict{Int,BasicBlock}()
        bbs[-1] = start
        bbs[-2] = finish
        new(bbs, start, -3, true, 0, Symbol[])
    end
end

type BlockLiveness
    basic_blocks :: Dict{Int,BasicBlock}
    depth_first_numbering

    function BlockLiveness(bb, dfn)
      new (bb, dfn)
    end
end

function show(io::IO, bl::BlockLiveness)
    println(io)
    body_order = getBbBodyOrder(bl)
    for i = 1:length(body_order)
      bb = bl.basic_blocks[body_order[i]]
      show(io, bb)
      println(io)
    end
end

function getMaxBB(bl::BlockLiveness)
    dprintln(3,"getMaxBB = ", length(bl.basic_blocks), " ", collect(keys(bl.basic_blocks)))
    maximum(collect(keys(bl.basic_blocks)))
end

function getMinBB(bl::BlockLiveness)
    dprintln(3,"getMinBB = ", length(bl.basic_blocks), " ", collect(keys(bl.basic_blocks)))
    minimum(collect(keys(bl.basic_blocks)))
end

type UpdateLabelState
    old_label
    new_label
    changed

    function UpdateLabelState(oldl, newl)
      new(oldl, newl, false)
    end
end

function update_label(x, state :: UpdateLabelState, top_level_number, is_top_level, read)
    asttype = typeof(x)
    
    if asttype == Expr
      head = x.head
      args = x.args
      if head == :gotoifnot
        else_label = args[2]
        dprintln(3,"else_label = ", else_label, " old = ", state.old_label, " new = ", state.new_label)
        assert(else_label == state.old_label)
        x.args[2] = state.new_label
        state.changed = true
        return x
      end
    elseif asttype == GotoNode
      assert(x.label == state.old_label)
      state.changed = true
      return GotoNode(state.new_label)
    end

    return nothing
end

function changeEndingLabel(bb, after :: BasicBlock, new_bb :: BasicBlock)
    state = UpdateLabelState(after.label, new_bb.label)
    dprintln(2, "changeEndingLabel ", bb.statements[end].expr)
    new_last_stmt = AstWalker.AstWalk(bb.statements[end].expr, update_label, state)
    assert(state.changed)
    assert(isa(new_last_stmt,Array))
    assert(length(new_last_stmt) == 1)
    bb.statements[end].expr = new_last_stmt[1]
end

# TODO: Todd, should not we update loop member info as well?
function insertBefore(bl::BlockLiveness, after :: Int, excludeBackEdge :: Bool = false, back_edge = nothing)
    dprintln(2,"insertBefore ", after)
    assert(haskey(bl.basic_blocks, after))
    dump_bb(bl)

    bb_after = bl.basic_blocks[after]

    if after < -2
      new_bb_id = getMinBB(bl) - 1
    else 
      new_bb_id = getMaxBB(bl) + 1
    end

    dprintln(2,"new_bb_id = ", new_bb_id)

    # Create the new basic block.
    new_bb = BasicBlock(new_bb_id)
    push!(new_bb.succs, bb_after)
    
    for pred in bb_after.preds
        if !excludeBackEdge || pred.label != back_edge
            push!(new_bb.preds, pred)
        end
    end
    new_bb.live_in = copy(bb_after.live_in)
    new_bb.live_out = copy(new_bb.live_in)
    bl.basic_blocks[new_bb_id] = new_bb

    # Since new basic block id is positive and the successor basic block is also positive, we
    # need to jump at the end of the new basic block to its successor.
    new_goto_stmt = nothing
    if after > -2
      new_goto_stmt = TopLevelStatement(-1, GotoNode(after))
    end

    bb_after.preds  = Set{BasicBlock}()
    push!(bb_after.preds, new_bb)

    # Sanity check that if a block has multiple incoming edges that it must have a positive label.
    if length(new_bb.preds) > 1
      assert(after > -2)
    end

    for pred in new_bb.preds
      dprintln(2,"pred = ", pred.label)
      replaceSucc(pred, bb_after, new_bb)
    end

    bl.depth_first_numbering = compute_dfn(bl.basic_blocks)
    dump_bb(bl)
    (new_bb, new_goto_stmt)
end

function getMaxStatementNum(bb :: BasicBlock)
    res = 0

    for s in bb.statements
      res = max(res, s.index)
    end

    return res
end

function getDistinctStatementNum(bl :: BlockLiveness)
    res = 0

    for bb in values(bl.basic_blocks)
      res = max(res, getMaxStatementNum(bb))
    end

    return res + 1
end

# TODO: Todd, should not we update loop member info as well?
function insertBetween(bl::BlockLiveness, before :: Int, after :: Int)
    dprintln(2,"insertBetween before = ", before, " after = ", after)
    assert(haskey(bl.basic_blocks, before))
    assert(haskey(bl.basic_blocks, after))
    dump_bb(bl)

    bb_before = bl.basic_blocks[before]
    bb_after  = bl.basic_blocks[after]

    if after < -2
      new_bb_id = getMinBB(bl) - 1
    else 
      new_bb_id = getMaxBB(bl) + 1
    end

    after_is_fallthrough = (bb_before.fallthrough_succ.label == after)
    dprintln(2,"new_bb_id = ", new_bb_id, " after is fallthrough = ", after_is_fallthrough)

    # Create the new basic block.
    new_bb = BasicBlock(new_bb_id)
    push!(new_bb.preds, bb_before)
    push!(new_bb.succs, bb_after)
    if after_is_fallthrough
      new_bb.fallthrough_succ = bb_after
    end
    new_bb.live_in  = bb_before.live_out
    new_bb.live_out = new_bb.live_in
    bl.basic_blocks[new_bb_id] = new_bb

    # Hook up the new basic block id in the preds and succs of the before and after basic blocks.
    replaceSucc(bb_before, bb_after, new_bb)
    delete!(bb_after.preds, bb_before)
    push!(bb_after.preds, new_bb)

    # Since new basic block id is positive and the successor basic block is also positive, we
    # need to jump at the end of the new basic block to its successor.
    new_goto_stmt = nothing
    if after > -2 && !after_is_fallthrough
      new_goto_stmt = TopLevelStatement(getDistinctStatementNum(bl), GotoNode(after))
    end

    bl.depth_first_numbering = compute_dfn(bl.basic_blocks)
    
    dump_bb(bl)

    (new_bb, new_goto_stmt)
end

function addStatementToEndOfBlock(bl :: BlockLiveness, block, stmt)
    live_res = expr_state()
    live_res.basic_blocks = bl.basic_blocks
    live_res.cur_bb = block
    live_res.top_level_number = getDistinctStatementNum(bl)
    from_expr(stmt, 1, live_res, true, not_handled, nothing)
end

function getBbBodyOrder(bl :: BlockLiveness)
    res = Int64[]

    for i = 1:length(bl.depth_first_numbering)
      cur = bl.depth_first_numbering[i]
      if !in(cur, res)
        push!(res, cur)
        cur_bb = bl.basic_blocks[cur]
        if cur_bb.fallthrough_succ != nothing
          fallthrough_id = cur_bb.fallthrough_succ.label
          assert(!in(fallthrough_id, res))
          push!(res, fallthrough_id) 
        end
      end
    end

    return res
end

function createFunctionBody(bl :: BlockLiveness)
    res = Any[]

    dprintln(2,"createFunctionBody, dfn = ", bl.depth_first_numbering)

    to_be_processed = deepcopy(bl.depth_first_numbering)

    while length(to_be_processed) != 0
      cur_block = shift!(to_be_processed)  # pop from front
      bb = bl.basic_blocks[cur_block]
      dprintln(2,"dumping basic block ", cur_block, " fallthrough = ", bb.fallthrough_succ == nothing ? "nothing" : bb.fallthrough_succ.label, " to_be_processed = ", to_be_processed)

      # Add label to the code.
      if cur_block >= 0
        push!(res, LabelNode(cur_block))
      end

      # Add the basic block's statements to the body.
      for i = 1:length(bb.statements)
        push!(res, bb.statements[i].expr) 
      end

      if bb.fallthrough_succ != nothing
        fallthrough_id = bb.fallthrough_succ.label
        assert(in(fallthrough_id, to_be_processed))
        filter!(x -> x != fallthrough_id, to_be_processed)
        unshift!(to_be_processed, fallthrough_id)    # push to the front of the dequeue
        dprintln(2,"moving fallthrough ", fallthrough_id, " to front, to_be_processed = ", to_be_processed)
      end
    end

    return res
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
      if stmts[j].index == top_number
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
      if stmts[j].index == top_number
        return bb[1]
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

function compute_dfn_internal(basic_blocks, cur_bb, cur_dfn, visited, bbs_df_order)
    push!(visited, cur_bb)

    bb = basic_blocks[cur_bb]

    for i in bb.succs
        if !in(i.label, visited)
            cur_dfn = compute_dfn_internal(basic_blocks, i.label, cur_dfn, visited, bbs_df_order)
        end
    end

    bbs_df_order[cur_dfn] = cur_bb
    bb.depth_first_number = cur_dfn
    cur_dfn - 1
end

function compute_dfn(basic_blocks)
    visited = Set()
    num_bb = length(basic_blocks)
    impossible_bb = -(num_bb + 3)
    bbs_df_order = [impossible_bb for i = 1:num_bb]
    compute_dfn_internal(basic_blocks, -1, num_bb, visited, bbs_df_order)
    if in(impossible_bb, bbs_df_order)
        dprintln(0,"bbs_df_order = ", bbs_df_order)
        throw(string("Problem with depth first basic block ordering.  Some dfn entry was not set."))
    end
    bbs_df_order
end

type Loop
    head :: Int
    back_edge :: Int
    members :: Set{Int}

    function Loop(h :: Int, b :: Int, m :: Set{Int})
      new (h, b, m)
    end
end

type DomLoops
    dom_dict :: Dict{Int,Set}
    loops :: Array{Loop,1}
end

function flm_internal(cur_bb, members, bbs)
    if !in(cur_bb, members)
        bb = bbs[cur_bb]
        push!(members, cur_bb)

        for pred in bb.preds
            flm_internal(pred.label, members, bbs)
        end
    end
    members
end

function findLoopMembers(head, back_edge, bbs)
    members = Set(head)
    flm_internal(back_edge, members, bbs)
end

function compute_dom_loops(bl::BlockLiveness)
    change_found = true
    bbs_df_order = bl.depth_first_numbering
    num_bb = length(bl.basic_blocks)
    assert(num_bb == length(bbs_df_order))

    all_set = Set()
    for i in collect(keys(bl.basic_blocks))
        push!(all_set, i)
    end
    dom_dict = Dict{Int,Set}()
    for i in collect(keys(bl.basic_blocks))
        if i == -1
            dom_dict[i] = Set(-1)
        else
            dom_dict[i] = deepcopy(all_set)
        end
    end

    count = 0;

    while(change_found)
        dprintln(3,"compute_dom_loops: dom_dict = ", dom_dict)

        count = count + 1
        if count > 1000
            throw(string("Probable infinite loop in compute_dom_loops."))
        end

        change_found = false

        for i = 1:num_bb
            bb_index = bbs_df_order[i]
            bb = bl.basic_blocks[bb_index]

            if bb_index != -1
                if length(bb.preds) != 0
                    pred_array = collect(bb.preds)
                    vb = deepcopy(dom_dict[pred_array[1].label])
                    for j = 2:length(pred_array)
                        vb = intersect(vb, dom_dict[pred_array[j].label])
                    end
                    push!(vb, bb_index)
                    if vb != dom_dict[bb_index]
                        dom_dict[bb_index] = vb
                        change_found = true
                    end
                end
            end
        end
    end

    loops = Loop[]

    for i = 1:num_bb
        bb_index = bbs_df_order[i]
        bb = bl.basic_blocks[bb_index]
        succ_array = collect(bb.succs)
        for j in succ_array
            local succ_id = j.label
            if in(succ_id, dom_dict[bb_index])
                members = findLoopMembers(succ_id, bb_index, bl.basic_blocks)
                dprintln(3,"loop members = ", members, " type = ", typeof(members))
                new_loop = Loop(succ_id, bb_index, members)
                dprintln(3,"new_loop = ", new_loop, " type = ", typeof(new_loop))
                push!(loops, new_loop)
            end
        end
    end

    DomLoops(dom_dict, loops)
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
    bbs = state.basic_blocks

    # Compute the inter-block live ranges.
    while found_change
        found_change = false

        for i = length(dfn):-1:1
            bb_index = dfn[i]
            bb = bbs[bb_index]

            accum = Set()
            if bb_index == -2
              # Special case for final block.
              # Treat input arrays as live at end of function.
              accum = Set{Symbol}(state.ref_params)
              dprintln(3,"Final block live_out = ", accum)
            else
              for j in bb.succs
                  accum = union(accum, j.live_in)
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
        bb = bbs[dfn[i]]

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

function connect_finish(state)
    connect(state.cur_bb, state.basic_blocks[-2], true)
end

function dump_bb(bl :: BlockLiveness)
    if DEBUG_LVL >= 4
      f = open("bbs.dot","w")
      println(f, "digraph bbs {")
    end

    body_order = getBbBodyOrder(bl)
    if DEBUG_LVL >= 3
      println("body_order = ", body_order)
    end

    for i = 1:length(body_order)
        bb = bl.basic_blocks[body_order[i]]
        dprint(2,bb)

        if DEBUG_LVL >= 4
            for j in bb.succs
                println(f, bb.label, " -> ", j.label, ";")
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
  state.ref_params = get_ref_params(param, meta[2])
  dprintln(3,"from_lambda: ref_params = ", state.ref_params)
  from_expr(body, depth, state, false, callback, cbdata)
end

# sequence of expressions
# ast = [ expr, ... ]
function from_exprs(ast::Array{Any,1}, depth, state, callback, cbdata)
  local len = length(ast)
  top_level = (state.top_level_number == 0)
  for i = 1:len
    if top_level
        state.top_level_number = i
        dprintln(2,"Processing top-level ast #",i," depth=",depth)
    else
        dprintln(2,"Processing ast #",i," depth=",depth)
    end
    dprintln(3,"ast[", i, "] = ", ast[i])
    from_expr(ast[i], depth, state, top_level, callback, cbdata)
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
    from_expr(rhs, depth, state, false, callback, cbdata)
  end
  dprintln(3,"liveness from_assignment handling lhs")
  state.read = false
  from_expr(lhs, depth, state, false, callback, cbdata)
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
      from_expr(fun, depth, state, false, callback, cbdata)
  end

  for i = 1:length(args)
    argtyp = typeof(args[i])
    dprintln(2,"cur arg = ", args[i], " type = ", argtyp)

    if(argtyp == Symbol)
      from_expr(args[i], depth+1, state, false, callback, cbdata)
    elseif argtyp == SymbolNode
      if isbits(args[i].typ)
        from_expr(args[i], depth+1, state, false, callback, cbdata)
      else
        from_expr(args[i], depth+1, state, false, callback, cbdata)
        if unmodified_args[i] == 1
          from_expr(args[i], depth+1, state, false, callback, cbdata)
        else
          state.read = false
          from_expr(args[i], depth+1, state, false, callback, cbdata)
          state.read = true
        end
      end
    else
      from_expr(args[i], depth+1, state, false, callback, cbdata)
    end
  end
end

function replaceSucc(cur_bb, orig_succ, new_succ)
  delete!(cur_bb.succs, orig_succ)   # delete the original successor from the set of successors
  push!(cur_bb.succs, new_succ)      # add the new successor to the set of successors

  if cur_bb.fallthrough_succ == orig_succ
    cur_bb.fallthrough_succ = new_succ
  else
    changeEndingLabel(cur_bb, orig_succ, new_succ)
  end
end

function removeUselessBlocks(bbs)
  found_change = true

  while found_change
    found_change = false

    for i in bbs
      bb = i[2]
      # eliminate basic blocks with only one successor and no statements.
      if length(bb.succs) == 1 && length(bb.statements) == 0
        succ = first(bb.succs)
        if succ.label != -2
          delete!(succ.preds, bb)

          for j in bb.preds
            replaceSucc(j, bb, succ)
            push!(succ.preds, j)
          end

          dprintln(3,"Removing block with no statements and one successor. ", bb)
          delete!(bbs, i[1])
          found_change = true
        end
      elseif length(bb.preds) == 1 && length(bb.succs) == 1
        pred = first(bb.preds)
        succ = first(bb.succs)
        if length(pred.succs) == 1 && succ.label != -2
            replaceSucc(pred, bb, succ) 
            delete!(succ.preds, bb)
            push!(succ.preds, pred)
            append!(pred.statements, bb.statements)
            used_in_pred = union(pred.def, pred.use)
            pred.def = union(pred.def, setdiff(bb.def, used_in_pred))
            pred.use = union(pred.use, setdiff(bb.use, used_in_pred))
            dprintln(3,"Removing block with only one predecessor and successor. ", bb)
            delete!(bbs, i[1])
            found_change = true
        end
      elseif length(bb.preds) == 0 && bb.label != -1
        # dead code
        for j in bb.succs
          delete!(j.preds, bb)
        end

        dprintln(3,"Removing dead block. ", bb)
        delete!(bbs, i[1])
        found_change = true
      end
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
function from_expr(ast::Any)
  from_expr(ast, not_handled, nothing)
end

function from_expr(ast::Any, callback, cbdata)
  dprintln(2,"from_expr Any")
  dprintln(3,ast)
  live_res = expr_state()
  from_expr(ast, 1, live_res, false, callback, cbdata)
  connect_finish(live_res)
# This is buggy and not adding any real value so I'm removing it for now.
#  dprintln(3,"before removeUselessBlocks ", length(live_res.basic_blocks), " ", live_res.basic_blocks)
#  removeUselessBlocks(live_res.basic_blocks)
#  dprintln(3,"after removeUselessBlocks ", length(live_res.basic_blocks), " ", live_res.basic_blocks)
  dfn = compute_dfn(live_res.basic_blocks)
  dprintln(3,"dfn = ", dfn)
  compute_live_ranges(live_res, dfn)
  dprintln(2,"Dumping basic block info from_expr.")
  ret = BlockLiveness(live_res.basic_blocks, dfn)
  dump_bb(ret)
  return ret
end

function from_label(label, state, callback, cbdata)
    dprintln(2,"LabelNode: ", label)
    if !haskey(state.basic_blocks,label)
        state.basic_blocks[label] = BasicBlock(label)
    end
    connect(state.cur_bb, state.basic_blocks[label], true)
    state.cur_bb = state.basic_blocks[label] 
    nothing
end

function from_goto(label, state, callback, cbdata)
    dprintln(2,"GotoNode: ", label)
    if !haskey(state.basic_blocks,label)
        state.basic_blocks[label] = BasicBlock(label)
    end
    connect(state.cur_bb, state.basic_blocks[label], false)
    state.cur_bb = nothing
    # The next statement should be a label so cur_bb will be set there.
    nothing
end

function from_return(args, depth, state, callback, cbdata)
    dprintln(2,"Expr return: ")
    from_exprs(args, depth, state, callback, cbdata)
    # connect this basic block to the finish pseudo-basic block
    connect(state.cur_bb, state.basic_blocks[-2], false)
    state.cur_bb = nothing
    nothing
end

function from_if(args, depth, state, callback, cbdata)
    # The structure of the if node is an array of length 2.
    assert(length(args) == 2)
    # The first index is the conditional.
    if_clause  = args[1]
    # The second index is the label of the else section.
    else_label = args[2]

    # Process the conditional as part of the current basic block.
    from_expr(if_clause, depth, state, false, callback, cbdata)

    implied = state.next_if
    # Prepare this for the next if part basic block.
    state.next_if = state.next_if - 1

    # Use negative number for the implicit block after the conditional.
    # Create the basic block for the if part and make that the current basic block.
    state.basic_blocks[implied] = BasicBlock(implied)

    if haskey(state.basic_blocks,else_label) == false
        # Create a basic block for the else portion.
        state.basic_blocks[else_label] = BasicBlock(else_label)
    end

    connect(state.cur_bb, state.basic_blocks[implied], true)
    connect(state.cur_bb, state.basic_blocks[else_label], false)

    state.cur_bb = state.basic_blocks[implied]
    nothing
end

function from_expr(ast::Any, depth, state, top_level, callback, cbdata)
  if typeof(ast) == LambdaStaticData
      # ast = uncompressed_ast(ast)
      # skip processing LambdaStaticData
      return nothing
  end
  local asttyp = typeof(ast)
  dprintln(2,"from_expr depth=",depth," ", " asttyp = ", asttyp)

  handled = callback(ast, cbdata)
  if handled != nothing
    addStatement(top_level, state, ast)
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
        from_expr(ast[i], depth, state, false, callback, cbdata)
    end
  elseif asttyp == Expr
    addStatement(top_level, state, ast)

    dprint(2,"Expr ")
    local head = ast.head
    local args = ast.args
    local typ  = ast.typ
    dprintln(2,head, " ", args)
    if head == :lambda
        from_lambda(args, depth, state, callback, cbdata)
    elseif head == :body
        from_exprs(args, depth+1, state, callback, cbdata)
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
    elseif head == :assertEqShape
        #addStatement(top_level, state, ast)
        assert(length(args) == 2)
        #dprintln(3,"liveness: assertEqShape ", args[1], " ", args[2], " ", typeof(args[1]), " ", typeof(args[2]))
        add_access(state.cur_bb, args[1].name, state.read, state.top_level_number)
        add_access(state.cur_bb, args[2].name, state.read, state.top_level_number)
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
    from_label(ast.label, state, callback, cbdata)
#    addStatement(top_level, state, ast)
  elseif asttyp == GotoNode
    addStatement(top_level, state, ast)
    from_goto(ast.label, state, callback, cbdata)
  elseif asttyp == Symbol
    addStatement(top_level, state, ast)
    dprintln(2,"Symbol type ", ast)
    add_access(state.cur_bb, ast, state.read, state.top_level_number)
  elseif asttyp == LineNumberNode
    #skip
  elseif asttyp == SymbolNode # name, typ
    addStatement(top_level, state, ast)
    dprintln(2,"SymbolNode type ", ast.name, " ", ast.typ)
    add_access(state.cur_bb, ast.name, state.read, state.top_level_number)
  elseif asttyp == TopNode    # name
    #skip
  elseif isdefined(:GetfieldNode) && asttyp == GetfieldNode  # GetfieldNode = value + name
    addStatement(top_level, state, ast)
    dprintln(3,"GetfieldNode type ",typeof(ast.value), " ", ast)
  elseif isdefined(:GlobalRef) && asttyp == GlobalRef
    addStatement(top_level, state, ast)
    dprintln(3,"GlobalRef type ",typeof(ast.mod), " ", ast)  # GlobalRef = mod + name
  elseif asttyp == QuoteNode
    addStatement(top_level, state, ast)
    local value = ast.value
    #TODO: fields: value
    dprintln(3,"QuoteNode type ",typeof(value))
  # elseif asttyp == Int64 || asttyp == Int32 || asttyp == Float64 || asttyp == Float32
  elseif isbits(asttyp)
    addStatement(top_level, state, ast)
    #skip
  elseif asttyp.name == Array.name
    addStatement(top_level, state, ast)
    dprintln(3,"Handling case of AST node that is an array. ast = ", ast, " typeof(ast) = ", asttyp)
    for i = 1:length(ast)
      from_expr(ast[i], depth, state, false, callback, cbdata)
    end
  elseif asttyp == DataType
    addStatement(top_level, state, ast)
  elseif asttyp == ()
    addStatement(top_level, state, ast)
  elseif asttyp == ASCIIString
    addStatement(top_level, state, ast)
  elseif asttyp == NewvarNode
    addStatement(top_level, state, ast)
  elseif asttyp == Nothing
    addStatement(top_level, state, ast)
  elseif asttyp == AccessSummary
    dprintln(3, "Incorporating AccessSummary")
    for i in ast.use
      add_access(state.cur_bb, i, true, state.top_level_number)
    end
    for i in ast.def
      add_access(state.cur_bb, i, false, state.top_level_number)
    end  
  elseif asttyp == Module
    #skip
  else
    throw(string("from_expr: unknown AST type :", asttyp, " ", ast))
  end
  nothing
end

end

