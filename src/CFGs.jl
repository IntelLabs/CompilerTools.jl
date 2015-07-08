module CFGs

using CompilerTools.AstWalker

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

export from_exprs, set_debug_level, find_bb_for_statement, show

type TopLevelStatement
    index
    expr

    TopLevelStatement(i, ex) = new(i, ex)
end

function show(io::IO, tls::TopLevelStatement)
    print(io, "TLS ", tls.index)
    println(io, "Expr: ", tls.expr)
end

type BasicBlock
    label
    preds :: Set{BasicBlock}
    succs :: Set{BasicBlock}
    fallthrough_succ
    depth_first_number
    statements :: Array{TopLevelStatement,1}
 
    BasicBlock(label) = new(label, Set{BasicBlock}(), Set{BasicBlock}(), nothing, nothing, TopLevelStatement[])
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
    print(io," ) fallthrough = ", bb.fallthrough_succ == nothing ? "nothing" : bb.fallthrough_succ.label)

    if bb.depth_first_number != nothing
        println(io, " depth_first=", bb.depth_first_number)
    end

    tls = bb.statements
    if length(tls) == 0
        println(io,"Basic block without any statements.")
    end
    for j = 1:length(tls)
        println(io, "    ",tls[j].index, "  ", tls[j].expr)
    end
end

import Base.show

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
    top_level_number :: Int

    function expr_state()
        start  = BasicBlock(-1)
        finish = BasicBlock(-2)
        init   = Dict{Any,BasicBlock}
        bbs = Dict{Int,BasicBlock}()
        bbs[-1] = start
        bbs[-2] = finish
        new(bbs, start, -3, 0)
    end
end

type CFG
    basic_blocks :: Dict{Int,BasicBlock}
    depth_first_numbering

    function CFG(bb, dfn)
      new (bb, dfn)
    end
end

function show(io::IO, bl::CFG)
    println(io)
    body_order = getBbBodyOrder(bl)
    for i = 1:length(body_order)
      bb = bl.basic_blocks[body_order[i]]
      show(io, bb)
      println(io)
    end
end

function getMaxBB(bl::CFG)
    dprintln(3,"getMaxBB = ", length(bl.basic_blocks), " ", collect(keys(bl.basic_blocks)))
    maximum(collect(keys(bl.basic_blocks)))
end

function getMinBB(bl::CFG)
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

function update_label(x, state :: UpdateLabelState, top_level_number, is_top_level)
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
function insertBefore(bl::CFG, after :: Int, excludeBackEdge :: Bool = false, back_edge = nothing)
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

function getDistinctStatementNum(bl :: CFG)
    res = 0

    for bb in values(bl.basic_blocks)
      res = max(res, getMaxStatementNum(bb))
    end

    return res + 1
end

function insertBetween(bl::CFG, before :: Int, after :: Int)
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

function insertat!(a, value, idx)
   splice!(a, idx:idx, [value, a[idx]])
end

function insertStatementAfter(bl :: CFG, block, stmt_idx, new_stmt)
    insertStatementInternal(bl, block, stmt_idx, new_stmt, true)
end

function insertStatementBefore(bl :: CFG, block, stmt_idx, new_stmt)
    insertStatementInternal(bl, block, stmt_idx, new_stmt, false)
end

function insertStatementInternal(bl :: CFG, block, stmt_idx, new_stmt, after :: Bool)
    temp_bb = BasicBlock(-9999999999)
    live_res = expr_state()
    live_res.basic_blocks = bl.basic_blocks
    live_res.cur_bb = temp_bb
    live_res.top_level_number = getDistinctStatementNum(bl)
    from_expr(new_stmt, 1, live_res, true, not_handled, nothing)

    assert(length(temp_bb.statements) == 1)
    stmt = temp_bb.statements[1]

    for bb in bl.basic_blocks
      stmts = bb[2].statements
      # Scan each statement in this block for a matching statement number.
      for j = 1:length(stmts)
        if stmts[j].index == stmt_idx
          if after
            insertat!(stmts, stmt, j+1)
          else
            insertat!(stmts, stmt, j)
          end
          return nothing
        end
      end
    end
    assert(false) 
end

function addStatementToEndOfBlock(bl :: CFG, block, stmt)
    live_res = expr_state()
    live_res.basic_blocks = bl.basic_blocks
    live_res.cur_bb = block
    live_res.top_level_number = getDistinctStatementNum(bl)
    from_expr(stmt, 1, live_res, true, not_handled, nothing)
end

function getBbBodyOrder(bl :: CFG)
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

function createFunctionBody(bl :: CFG)
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

# Search for a statement with the given number in the liveness information.
function find_top_number(top_number::Int, bl::CFG)
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
function find_bb_for_statement(top_number::Int, bl::CFG)
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

function connect_finish(state)
    connect(state.cur_bb, state.basic_blocks[-2], true)
end

function dump_bb(bl :: CFG)
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

# :lambda expression
# ast = [ parameters, meta (local, types, etc), body ]
function from_lambda(ast::Array{Any,1}, depth, state, callback, cbdata)
  assert(length(ast) == 3)
  local param = ast[1]
  local meta  = ast[2]
  local body  = ast[3]
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
#      # eliminate basic blocks with only one successor and no statements.
#      if length(bb.succs) == 1 && length(bb.statements) == 0
#        succ = first(bb.succs)
#        if succ.label != -2
#          delete!(succ.preds, bb)
#
#          for j in bb.preds
#            replaceSucc(j, bb, succ)
#            push!(succ.preds, j)
#          end
#
#          dprintln(3,"Removing block with no statements and one successor. ", bb)
#          delete!(bbs, i[1])
#          found_change = true
#        end
#      elseif length(bb.preds) == 1 && length(bb.succs) == 1
#        pred = first(bb.preds)
#        succ = first(bb.succs)
#        if length(pred.succs) == 1 && succ.label != -2
#            replaceSucc(pred, bb, succ) 
#            delete!(succ.preds, bb)
#            push!(succ.preds, pred)
#            append!(pred.statements, bb.statements)
#            dprintln(3,"Removing block with only one predecessor and successor. ", bb)
#            delete!(bbs, i[1])
#            found_change = true
#        end
#      elseif length(bb.preds) == 0 && bb.label != -1
      if length(bb.preds) == 0 && bb.label != -1
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

# ENTRY
function from_ast(ast::Any)
  from_expr(ast, not_handled, nothing)
end

function from_expr(ast::Any, callback, cbdata)
  dprintln(2,"from_expr Any")
  dprintln(3,ast)
  live_res = expr_state()
  from_expr(ast, 1, live_res, false, callback, cbdata)
  connect_finish(live_res)
# I simplifed removeUselessBlocks to just get rid of dead blocks (i.e., no predecessor)
  dprintln(3,"before removeUselessBlocks ", length(live_res.basic_blocks), " ", live_res.basic_blocks)
  removeUselessBlocks(live_res.basic_blocks)
  dprintln(3,"after removeUselessBlocks ", length(live_res.basic_blocks), " ", live_res.basic_blocks)

  dfn = compute_dfn(live_res.basic_blocks)
  dprintln(3,"dfn = ", dfn)
  ret = CFG(live_res.basic_blocks, dfn)
  dprintln(2,"Dumping basic block info from_expr.")
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

  if asttyp == Expr
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
    elseif head == :return
        from_return(args,depth,state, callback, cbdata)
    elseif head == :gotoifnot
        from_if(args,depth,state, callback, cbdata)
    end
  elseif asttyp == LabelNode
    from_label(ast.label, state, callback, cbdata)
  elseif asttyp == GotoNode
    addStatement(top_level, state, ast)
    from_goto(ast.label, state, callback, cbdata)
  else
    addStatement(top_level, state, ast)
  end
  nothing
end

end

