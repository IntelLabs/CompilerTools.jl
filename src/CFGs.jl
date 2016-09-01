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

# The CFGs module provides the type CFG that contains the control-flow graph of a given function.
module CFGs

import ..DebugMsg
DebugMsg.init()

using CompilerTools
using CompilerTools.AstWalker
using CompilerTools.Helper

import Base.show


export from_exprs, find_bb_for_statement, show

"""
Data structure to hold the index (relative to the beginning of the body of the function) of a top-level statement
and the top-level statement itself.
"""
type TopLevelStatement
    index
    expr

    TopLevelStatement(i, ex) = new(i, ex)
end

"""
Overload of Base.show to pretty-print a TopLevelStatement.
"""
function show(io::IO, tls::TopLevelStatement)
    print(io, "TLS ", tls.index)
    println(io, "Expr: ", tls.expr)
end

const CFG_ENTRY_BLOCK = -1
const CFG_EXIT_BLOCK  = -2

"""
Data structure to hold information about one basic block in the control-flow graph.
This structure contains the following fields:
1) label - an Int.  If positive, this basic block corresponds to a basic block declared in the AST through a label node.
                    The special label value -1 corresponds to the starting basic blocks.  The special value -2
                    corresponds to the final basic block (to which everything must flow).  Negative values correspond to
                    implicit basic blocks following gotoifnot nodes.  There nodes may goto some (positive) label but if
                    that branch is not taken they fall-through into an unlabelled basic (in the AST at least) but we
                    give such blocks negative labels.
2) preds - a set of basic blocks from which control may reach the current basic block
3) succs - a set of basic blocks to which control may flow from the current basic block
4) fallthrough_succ - if not "nothing", this indicates which of the basic block successors is reached via falling through from
                    the current basic block rather than a jump (goto or gotoifnot)
5) depth_first_number - a depth first numbering of the basic block graph is performed and this basic block's number is stored here
6) statements - an array of the statements in this basic block.
"""
type BasicBlock
    label
    preds :: Set{BasicBlock}
    succs :: Set{BasicBlock}
    fallthrough_succ
    depth_first_number
    statements :: Array{TopLevelStatement,1}
 
    BasicBlock(label) = new(label, Set{BasicBlock}(), Set{BasicBlock}(), nothing, nothing, TopLevelStatement[])
end

"""
Adds a top-level statement just encountered during a partial walk of the AST.
First argument indicates if this statement is a top-level statement.
Second argument is a object collecting information about the CFG as we go along.
Third argument is some sub-tree of the AST.
"""
function addStatement(top_level, state, ast :: ANY)
    @dprintln(3, "addStatement ", ast, " ", top_level, " ", state.cur_bb == nothing)
    if top_level && state.cur_bb != nothing
        @dprintln(3,"liveness adding statement number ", state.top_level_number)
        for i in state.cur_bb.statements
          if i.index == state.top_level_number
            throw(string("statement number already there"))
          end
        end
        push!(state.cur_bb.statements, TopLevelStatement(state.top_level_number, ast))
        return true
    end
    return false
end

import Base.show

"""
Overload of Base.show to pretty-print a CFGS.BasicBlock object.
"""
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

"""
Connect the "from" input argument basic block to the "to" input argument basic block.
If the third argument "fallthrough" is true then the "to" block is also set as the "from" basic block's fallthrough successor.
"""
function connect(from, to, fallthrough)
    if from != nothing
        push!(from.succs,to)
        push!(to.preds,from)
        if fallthrough
          from.fallthrough_succ = to
        end
    end
end

"""
Collects information about the CFG as it is being constructed.
Contains a dictionary of the currently known basic blocks that maps the label to a BasicBlock object.
cur_bb is the currently active BasicBlock to which the next statement encountered should be added.
next_if contains the next negative label number to be used for the next needed implicit basic block label.
top_level_number is the last top-level statement added.
"""
type expr_state
    basic_blocks :: Dict{Int,BasicBlock}
    cur_bb
    next_if :: Int
    top_level_number :: Int

    function expr_state()
        start  = BasicBlock(CFG_ENTRY_BLOCK)
        finish = BasicBlock(CFG_EXIT_BLOCK)
        init   = Dict{Any,BasicBlock}
        bbs = Dict{Int,BasicBlock}()
        bbs[CFG_ENTRY_BLOCK] = start
        bbs[CFG_EXIT_BLOCK]  = finish
        new(bbs, start, -3, 0)
    end
end

"""
The main data structure to hold information about the control flow graph.
The basic_blocks field is a dictionary from basic block label to BasicBlock object.
The depth_first_numbering is an array of length the number of basic blocks.  
   Entry N in this array is the label of the basic block with depth-first numbering N.
"""
type CFG
    basic_blocks :: Dict{Int,BasicBlock}
    depth_first_numbering

    function CFG(bb, dfn)
      new(bb, dfn)
    end
end

"""
Overload of Base.show to pretty-print a CFG object.
"""
function show(io::IO, bl::CFG)
    println(io)
    body_order = getBbBodyOrder(bl)
    for i = 1:length(body_order)
      bb = bl.basic_blocks[body_order[i]]
      show(io, bb)
      println(io)
    end
end

"""
Returns the maximum basic block label for the given CFG.
"""
function getMaxBB(bl::CFG)
    @dprintln(3,"getMaxBB = ", length(bl.basic_blocks), " ", collect(keys(bl.basic_blocks)))
    maximum(collect(keys(bl.basic_blocks)))
end

"""
Returns the minimum basic block label for the given CFG.
"""
function getMinBB(bl::CFG)
    @dprintln(3,"getMinBB = ", length(bl.basic_blocks), " ", collect(keys(bl.basic_blocks)))
    minimum(collect(keys(bl.basic_blocks)))
end

"""
The opaque callback data type for the update_label callback.
It holds the old_label that should be changed to the new_label.
It also holds a "changed" field that starts as false and gets set to true when the callback actually
finds the old label and replaces it with the new one.
"""
type UpdateLabelState
    old_label
    new_label
    changed

    function UpdateLabelState(oldl, newl)
      new(oldl, newl, false)
    end
end

"""
An AstWalk callback that pattern matches GotoNode's and :gotoifnot Expr nodes and determines if the
label specified in this nodes is equal to the "old_label" in the UpdateLabelState and if so replaces
the "old_label" with "new_label" and sets the "changed" flag to true to indicate that update_label
was successful.
"""
function update_label(x::Expr,
                      state::UpdateLabelState,
                      top_level_number,
                      is_top_level,
                      read)
    head = x.head
    args = x.args
    if head == :gotoifnot
        # A :gotoifnot Expr node with the else_label in args[2]
        else_label = args[2]
        @dprintln(3,"else_label = ", else_label, " old = ", state.old_label, " new = ", state.new_label)
        # Assert that this :gotoifnot Expr node's label is the old_label that we have been instructed to replace.
        assert(else_label == state.old_label)
        # Update the current :gotoifnot Expr node in place.
        x.args[2] = state.new_label
        # Mark as successful label replacement.
        state.changed = true
        # Indicate we changed the current node.
        return x
    end

    # Indicate we didn't change anything.
    return CompilerTools.AstWalker.ASTWALK_RECURSE
end

function update_label(x::GotoNode,
                      state::UpdateLabelState,
                      top_level_number,
                      is_top_level,
                      read)
    # The node is a GotoNode which has a "label" field.
    # Assert that this GotoNode's label field is the old_label that we have been instructed to replace.
    assert(x.label == state.old_label)
    # Mark as successful label replacement.
    state.changed = true
    # Return a new node with the new label.
    # At some point there was a problem with updating the label in place as object's this type are considered immutable.
    return GotoNode(state.new_label)
end

function update_label(x::ANY,
                      state::UpdateLabelState,
                      top_level_number,
                      is_top_level,
                      read)
    # Indicate we didn't change anything.
    return CompilerTools.AstWalker.ASTWALK_RECURSE
end

"""
BasicBlock bb currently is known to contain a jump to the BasicBlock after.
This function changes bb so that it no longer jumps to after but to "new_bb" instead.
The jump has to be in the last statement of the BasicBlock.
AstWalk on the last statement of the BasicBlock is used with the update_label callback function.
"""
function changeEndingLabel(bb, after :: BasicBlock, new_bb :: BasicBlock)
    state = UpdateLabelState(after.label, new_bb.label)
    @dprintln(2, "changeEndingLabel ", bb.statements[end].expr)
    new_last_stmt = AstWalker.AstWalk(bb.statements[end].expr, update_label, state)
    assert(state.changed)
    bb.statements[end].expr = new_last_stmt
end

"""
Given a CFG in input parameter "bl" and a basic block label "after" in that CFG,
insert a new basic block into the CFG before block "after".  
Returns a tuple of the new basic block created and if needed a GotoNode AST node to be inserted at the end of the new
basic block so that it will jump to the "after" basic block.  The user of this function is expected to insert
at the end of the new basic block once they are done inserting their other code.
If "after" is the head of a loop, you can stop the basic block containing the loop's back edge from being added to 
the new basic block by setting excludeBackEdge to true and setting back_edge to the loop's basic block containing
the back edge.
"""
function insertBefore(bl::CFG, after :: Int, excludeBackEdge :: Bool = false, back_edge = nothing)
    @dprintln(2,"insertBefore ", after, " excludeBackEdge = ", excludeBackEdge, " back_edge = ", back_edge)
    assert(haskey(bl.basic_blocks, after))   # Make sure the basic block we want to insert before exists in the CFG.
    dump_bb(bl)                              # Print the CFG in debugging mode.

    bb_after = bl.basic_blocks[after]        # Get the BasicBlock corresponding to after's label.

    # Get the label for the new basic block.  If the block to insert before has a positive label
    # then we'll need to be able to jump to new basic block we are inserting as well so it has to have a
    # positive label, which we get by adding 1 to the previous maximum basic block level.
    # If the block we want to insert before has a negative level then similarly the new basic block also
    # has to be negative, which was get from the previous minimum -1.
    if after < CFG_EXIT_BLOCK
      new_bb_id = getMinBB(bl) - 1
    else 
      new_bb_id = getMaxBB(bl) + 1
    end

    @dprintln(2,"new_bb_id = ", new_bb_id)

    # Create the new basic block.
    new_bb = BasicBlock(new_bb_id)
    # Say that the "after" basic block can come after the new basic block.
    push!(new_bb.succs, bb_after)
    
    # For each predecessor of the "after" basic block...
    for pred in bb_after.preds
        # If this predecessor isn't a back-edge from a loop that we want to exclude...
        if !excludeBackEdge || pred.label != back_edge
            # ... then make this predecessor of "after" a predecessor of the new basic block ...
            push!(new_bb.preds, pred)
            # ... no longer include this predecessor as one for "after" but exclusively the new basic block.
            delete!(bb_after.preds, pred)
        end
    end
    # Add the new basic block to the CFG.
    bl.basic_blocks[new_bb_id] = new_bb

    # Since new basic block id is positive and the successor basic block is also positive, we
    # need to jump at the end of the new basic block to its successor.
    new_goto_stmt = nothing
    if after > CFG_EXIT_BLOCK
      new_goto_stmt = TopLevelStatement(-1, GotoNode(after))
    end

    # Indicate that the new basic block is a predecessor of the "after" basic block.
    push!(bb_after.preds, new_bb)

    # Sanity check that if a block has multiple incoming edges that it must have a positive label.
    if length(new_bb.preds) > 1
      assert(after > CFG_EXIT_BLOCK)
    end

    # For all the predecessors of the new basic block, go through and make those blocks successors
    # no longer point to "after" but point to the new basic block instead.
    for pred in new_bb.preds
      @dprintln(2,"pred = ", pred.label)
      replaceSucc(pred, bb_after, new_bb)
    end

    # Just have to recompute the depth-first numbering.
    bl.depth_first_numbering = compute_dfn(bl.basic_blocks)
    dump_bb(bl)
    (new_bb, new_goto_stmt)
end

"""
Get the maximum statement index for a given BasicBlock.
"""
function getMaxStatementNum(bb :: BasicBlock)
    res = 0

    for s in bb.statements
      res = max(res, s.index)
    end

    return res
end

"""
Get a possible new statement number by finding the maximum statement value in any BasicBlock in the given CFG and adding 1.
"""
function getDistinctStatementNum(bl :: CFG)
    res = 0

    for bb in values(bl.basic_blocks)
      res = max(res, getMaxStatementNum(bb))
    end

    return res + 1
end

function insertConditional(bl :: CFG, block_to_split :: Int, statement_in_block_to_split_at :: Int, cond_gotoifnot :: Expr, if_stmts :: Array{Any,1})
    @dprintln(2,"insertConditionalw condition = ", cond_gotoifnot, " block_to_split = ", block_to_split, " statement_to_split = ", statement_in_block_to_split_at)
    assert(haskey(bl.basic_blocks, block_to_split))
    assert(cond_gotoifnot.head == :gotoifnot)
    dump_bb(bl)                              # Print the CFG in debugging mode.
    bb = bl.basic_blocks[block_to_split]
    # NOT FINISHED YET!!!!!
end

"""
Modifies the CFG to create a conditional (i.e., if statement) that wraps a certain region of the CFG whose entry block is
"first" and whose last block is "last".
Takes a parameters:
1) bl - the CFG to modify
2) cond_gotoifnot - a :gotoifnot Expr whose label is equal to "first"
3) first - the existing starting block of the code to be included in the conditional
4) merge - the existing block to be executed after the conditional
To be eligible for wrapping, first and merge must be in the same scope of source code.
This restriction is validated by confirming that "first" dominates "merge" and that "merge" inverse dominates "first".
"""
function wrapInConditional(bl :: CFG, cond_gotoifnot :: Expr, first :: Int, merge :: Int, back_edge :: Union{Void, BasicBlock} = nothing)
    @dprintln(2,"wrapInConditional condition = ", cond_gotoifnot, " first = ", first, " merge = ", merge)
    assert(haskey(bl.basic_blocks, first))   # Make sure the "before" basic block exists in the CFG.
    assert(haskey(bl.basic_blocks, merge))   # Make sure the "after"  basic block exists in the CFG.
    dump_bb(bl)                              # Print the CFG in debugging mode.
    assert(cond_gotoifnot.head == :gotoifnot)
    cond_label = cond_gotoifnot.args[2]
    assert(cond_label == first)

    bb_first     = bl.basic_blocks[first]
    bb_merge     = bl.basic_blocks[merge]
    dom_dict     = compute_dominators(bl)
    inv_dom_dict = compute_inverse_dominators(bl)

    @assert in(merge, dom_dict[first])     "The starting block in wrapInConditional does not dominate the merge block."
    @assert in(first, inv_dom_dict[merge]) "The merge block in wrapInConditional does not inverse dominate the first block."

    # Get the label for the new basic block.  If the block to insert before has a positive label
    # then we'll need to be able to jump to new basic block we are inserting as well so it has to have a
    # positive label, which we get by adding 1 to the previous maximum basic block level.
    # If the block we want to insert before has a negative level then similarly the new basic block also
    # has to be negative, which was get from the previous minimum -1.
    if first < CFG_EXIT_BLOCK
      new_bb_id = getMinBB(bl) - 1
      cond_fallthrough = new_bb_id - 1
    else 
      new_bb_id = getMaxBB(bl) + 1
      cond_fallthrough = getMinBB(bl) - 1
    end

    @dprintln(2,"new_bb_id = ", new_bb_id, " cond_fallthrough = ", cond_fallthrough)

    # Create the new basic blocks.
    new_bb  = BasicBlock(new_bb_id)
    cond_ft = BasicBlock(cond_fallthrough)

    # The new basic block containing the conditional can go to the new fallthrough block or "first".
    push!(new_bb.succs, cond_ft)
    new_bb.fallthrough_succ = cond_ft
    push!(new_bb.succs, bb_first)
    #push!(new_bb.sttaements, TopLevelStatement(-1, cond_gotoifnot))

    # For each predecessor of the "after" basic block...
    for pred in bb_first.preds
        # If this predecessor isn't a back-edge from a loop that we want to exclude...
        if back_edge != nothing || pred.label != back_edge
            # ... then make this predecessor of "after" a predecessor of the new basic block ...
            push!(new_bb.preds, pred)
            # ... no longer include this predecessor as one for "after" but exclusively the new basic block.
            delete!(bb_first.preds, pred)
        end
    end

    # Link the conditional fallthrough's succs and preds.
    push!(cond_ft.succs, bb_merge)
    push!(cond_ft.preds, new_bb)
    push!(cond_ft.statements, TopLevelStatement(-1, GotoNode(merge)))
    push!(bb_merge.preds, cond_ft)

    # Add the new basic blocks to the CFG.
    bl.basic_blocks[new_bb_id] = new_bb
    bl.basic_blocks[cond_fallthrough] = cond_ft

    push!(bb_first.preds, new_bb)

    # For all the predecessors of the new basic block, go through and make those blocks successors
    # no longer point to "after" but point to the new basic block instead.
    for pred in new_bb.preds
      @dprintln(2,"pred = ", pred.label)
      replaceSucc(pred, bb_first, new_bb)
    end

    # Just have to recompute the depth-first numbering.
    bl.depth_first_numbering = compute_dfn(bl.basic_blocks)
    dump_bb(bl)
    (new_bb, cond_ft)
end

"""
Insert a new basic block into the CFG "bl" between the basic blocks whose labels are "before" and "after".
Returns a tuple of the new basic block created and if needed a GotoNode AST node to be inserted at the end of the new
basic block so that it will jump to the "after" basic block.  The user of this function is expected to insert
at the end of the new basic block once they are done inserting their other code.
"""
function insertBetween(bl :: CFG, before :: Int, after :: Int)
    @dprintln(2,"insertBetween before = ", before, " after = ", after)
    assert(haskey(bl.basic_blocks, before))   # Make sure the "before" basic block exists in the CFG.
    assert(haskey(bl.basic_blocks, after))    # Make sure the "after"  basic block exists in the CFG.
    dump_bb(bl)                               # Print the CFG in debugging mode.

    bb_before = bl.basic_blocks[before]       # Get the BasicBlock for "before".
    bb_after  = bl.basic_blocks[after]        # Get the BasicBlock for "after".

    @assert (in(bb_after, bb_before.succs)) "To insert between two blocks, the after block must be a successor of the before block, otherwise the operation is not well-defined."

    # Get the label for the new basic block.  If the block to insert before has a positive label
    # then we'll need to be able to jump to new basic block we are inserting as well so it has to have a
    # positive label, which we get by adding 1 to the previous maximum basic block level.
    # If the block we want to insert before has a negative level then similarly the new basic block also
    # has to be negative, which was get from the previous minimum -1.
    if after < CFG_EXIT_BLOCK
      new_bb_id = getMinBB(bl) - 1
    else 
      new_bb_id = getMaxBB(bl) + 1
    end

    # Determine if after is reached from before via a fallthrough or not.
    after_is_fallthrough = (bb_before.fallthrough_succ.label == after)
    @dprintln(2,"new_bb_id = ", new_bb_id, " after is fallthrough = ", after_is_fallthrough)

    # Create the new basic block.
    new_bb = BasicBlock(new_bb_id)
    push!(new_bb.preds, bb_before)  # The new basic block will have "before" as a predecessor.
    push!(new_bb.succs, bb_after)   # The new basic block will have "after" as a successor.
    # If after was previously reached from before via fallthrough then after will now be reached
    # from the new basic block via fallthrough as well.
    if after_is_fallthrough
      new_bb.fallthrough_succ = bb_after
    end
    bl.basic_blocks[new_bb_id] = new_bb  # Add the new basic block to the CFG.

    # Hook up the new basic block id in the preds and succs of the before and after basic blocks.
    replaceSucc(bb_before, bb_after, new_bb)
    delete!(bb_after.preds, bb_before)
    push!(bb_after.preds, new_bb)

    # Since new basic block id is positive and the successor basic block is also positive, we
    # need to jump at the end of the new basic block to its successor.
    new_goto_stmt = nothing
    if after > CFG_EXIT_BLOCK && !after_is_fallthrough
      new_goto_stmt = TopLevelStatement(getDistinctStatementNum(bl), GotoNode(after))
    end

    # Just have to recompute the depth-first numbering.
    bl.depth_first_numbering = compute_dfn(bl.basic_blocks)
    dump_bb(bl)

    (new_bb, new_goto_stmt)
end

"""
Insert into an array "a" with a given "value" at the specified index "idx".
"""
function insertat!(a, value, idx)
   splice!(a, idx:idx, [value, a[idx]])
end

"""
For a given CFG "bl" and a "block" in that CFG, add a new statement "new_stmt" to the basic block
after statement index "stmt_idx".
"""
function insertStatementAfter(bl :: CFG, block, stmt_idx, new_stmt)
    insertStatementInternal(bl, block, stmt_idx, new_stmt, true)
end

"""
For a given CFG "bl" and a "block" in that CFG, add a new statement "new_stmt" to the basic block
before statement index "stmt_idx".
"""
function insertStatementBefore(bl :: CFG, block, stmt_idx, new_stmt)
    insertStatementInternal(bl, block, stmt_idx, new_stmt, false)
end

function insertStatementBeginningOfBlock(bl :: CFG, block, new_stmt)
    temp_bb = BasicBlock(-9999999999)
    live_res = expr_state()
    live_res.basic_blocks = bl.basic_blocks
    live_res.cur_bb = temp_bb
    live_res.top_level_number = getDistinctStatementNum(bl)
    from_expr(new_stmt, 1, live_res, true, not_handled, nothing)

    assert(length(temp_bb.statements) == 1)
    stmt = temp_bb.statements[1]

    if length(block.statements) > 0
        insertat!(block.statements, stmt, 1)
    else
        push!(block.statements, stmt)
    end
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

"""
Given a CFG "bl" and a basic "block", add statement "stmt" to the end of that block.
"""
function addStatementToEndOfBlock(bl :: CFG, block, stmt)
    live_res = expr_state()
    live_res.basic_blocks = bl.basic_blocks
    live_res.cur_bb = block
    # We set the top-level number of the new statement equal to a guaranteed unique such number via a call to getDistinctStatementNum.
    live_res.top_level_number = getDistinctStatementNum(bl)
    # Use from_expr just like we were originally parsing the function to get it to add.
    # To set this up, we need an expr_state in live_res whose current basic block is set
    # to the one that we wish to add to.
    from_expr(stmt, 1, live_res, true, not_handled, nothing)
end

"""
Determine a valid and reasonable order of basic blocks in which to reconstruct a :body Expr.
Also useful for printing in a reasonable order.
-1 (the starting block should always be first)
-2 (the exit block should always come last)
If there is a block that fallsthrough to return then that block should come next to last.
"""
function getBbBodyOrder(bl :: CFG)
    res  = Int64[]
    rev  = Int64[CFG_EXIT_BLOCK]
    used = Set{Int64}(CFG_EXIT_BLOCK)

    found = true
    while found == true
        found = false
        last = rev[end]
        last_bb = bl.basic_blocks[last]

        @dprintln(3, "getBbBodyOrder reverse fallthrough ", last, " ", last_bb, " ", rev, " ", used)
        for pred in last_bb.preds
            @dprintln(3, "pred = ", pred)
            if pred.fallthrough_succ != nothing
                @dprintln(3, "fallthrough")
                if pred.fallthrough_succ.label == last
                    @dprintln(3, "will add")
                    push!(rev, pred.label)
                    push!(used, pred.label)
                    found = true
                end
            end
        end
    end

    total_blocks = length(bl.depth_first_numbering)

    # A reasonable order is just the depth first numbering but just using this can result in fallthrough nodes
    # not coming right after their predecessor.
    for i = 1:total_blocks
      cur = bl.depth_first_numbering[i]
      @dprintln(3, "getBbBodyOrder forward ", cur, " ", rev, " ", used, " ", res)
      # If the next block via the depth_first_number is not already in the body order do the following.
      # This can happen if a fallthrough successor is added before its normal place in depth first numbering.
      if !in(cur, used)
        cur_bb = bl.basic_blocks[cur]  # Get the BasicBlock given the current block's index.
        @dprintln(3, "cur_bb = ", cur_bb, " ", used, " ", res)
        push!(res, cur)                # Add this basic block to the body order.
        push!(used, cur)
        # If the cur basic block has a fallthrough successor then make sure it comes next
        # by adding it to the body order here.
        while cur_bb.fallthrough_succ != nothing
          fallthrough_id = cur_bb.fallthrough_succ.label
          assert(!in(fallthrough_id, res))
          push!(res, fallthrough_id) 
          push!(used, fallthrough_id)
          cur_bb = cur_bb.fallthrough_succ
          @dprintln(3, "cur_bb = ", cur_bb, " ", used, " ", res)
        end
      end
    end

    append!(res, reverse(rev))

    return res
end

"""
Create the array of statements that go in a :body Expr given a CFG "bl".
"""
function createFunctionBody(bl :: CFG)
    res = Any[]

    body_order = getBbBodyOrder(bl)
    @dprintln(2,"createFunctionBody, body_order = ", body_order)

    # Go through the blocks in body order.
    for bo = 1:length(body_order)
      # Get the label of the next block to output.
      cur_block = body_order[bo]
      # Get the BasicBlock corresponding to the label.
      bb = bl.basic_blocks[cur_block]
      @dprintln(2,"dumping basic block ", cur_block, " fallthrough = ", bb.fallthrough_succ == nothing ? "nothing" : bb.fallthrough_succ.label)

      # Labels greater than or equal to 0 are real and are output to the beginning of the block.
      if cur_block >= 0
        push!(res, LabelNode(cur_block))
      end

      # Add the basic block's statements to the body.
      for i = 1:length(bb.statements)
        if bb.statements[i].expr != nothing 
          push!(res, bb.statements[i].expr) 
        end
      end
    end

    @dprintln(3,"createFunctionBody res = ", res)

    return res
end

"""
Search for a statement with the given number in the CFG "bl".
Returns the statement corresponding to the given number or "nothing" if the statement number is not found.
"""
function find_top_number(top_number::Int, bl::CFG)
  # For each block.
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
end

"""
Find the basic block that contains a given statement number.
Returns the basic block label of the basic block that contains the given statement number or "nothing" if the statement number is not found.
"""
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

  @dprintln(3,"Didn't find statement top_number in basic_blocks.")
  nothing
end

"""
The recursive heart of depth first numbering.
"""
function compute_dfn_internal(basic_blocks, cur_bb, cur_dfn, visited, bbs_df_order)
    push!(visited, cur_bb)        # Mark that we've seen the current incoming basic block.

    bb = basic_blocks[cur_bb]     # Get the BasicBlock corresponding to the incoming basic block label cur_bb.

    # For each successor of the current basic block.
    for i in bb.succs
        # If it hasn't already been visited, then recursively visit it.
        if !in(i.label, visited)
            cur_dfn = compute_dfn_internal(basic_blocks, i.label, cur_dfn, visited, bbs_df_order)
        end
    end

    bbs_df_order[cur_dfn] = cur_bb    # Store the current basic block's label in the whole depth first numbering array.
    bb.depth_first_number = cur_dfn   # Store the depth first number in the current basic block.
    cur_dfn - 1                       # Decrement the next depth first number to use.
end

"""
Computes the depth first numbering of the basic block graph.
"""
function compute_dfn(basic_blocks)
    # This routine is initialization for the algorithm and post-algorithm checking.  compute_dfn_internal does the real work (recursively).
    visited = Set()                       # Initialize the set of visited nodes to 
    num_bb = length(basic_blocks)         # Determine the length of the depth first numbering array
    impossible_bb = -(num_bb + 3)         # Computes a sentinel value that is an impossible basic block label given the number of basic blocks.
    bbs_df_order = [impossible_bb for i = 1:num_bb]  # Initializes an array full of those sentinel values.
    compute_dfn_internal(basic_blocks, CFG_ENTRY_BLOCK, num_bb, visited, bbs_df_order)  # Do the recursive process to compute the numbering starting from the first basic block -1.
    # Make sure that all basic blocks were visited during the recursively numbering process by making sure all impossible_bb values were over-written.
    if in(impossible_bb, bbs_df_order)
        @dprintln(0,"bbs_df_order = ", bbs_df_order)
        throw(string("Problem with depth first basic block ordering.  Some dfn entry was not set."))
    end
    bbs_df_order
end

"""
Connect the current basic block as a fallthrough to the final invisible basic block (-2).
"""
function connect_finish(state)
    connect(state.cur_bb, state.basic_blocks[CFG_EXIT_BLOCK], true)
end

"""
Prints a CFG "bl" with varying degrees of verbosity from debug level 2 up to 4.
Additionally, at debug level 4 and graphviz bbs.dot file is generated that can be used to visualize the basic block structure of the function.
"""
function dump_bb(bl :: CFG)
    if DEBUG_LVL >= 4
      filename = string(tempname(),".dot")
      println("Creating dot file ", filename)
      f = open(filename,"w")
      println(f, "/* dot -Tjpg bbs.dot -o bbs.jpg */")
      println(f, "digraph bbs {")
    end

    body_order = getBbBodyOrder(bl)
    if DEBUG_LVL >= 3
      println("body_order = ", body_order)
    end

    for i = 1:length(body_order)
        bb = bl.basic_blocks[body_order[i]]
        @dprint(2,bb)

        if DEBUG_LVL >= 4
            println("Dumping succs for ", body_order[i])
            for j in bb.succs
                println("j = ", j)
                print(f, bb.label, " -> ", j.label)
                if bb.fallthrough_succ == j
                  println("isfallthrough")
                  print(f, " [color=\"red\"]")
                end
                println(f, ";")
            end
        end
    end

    if DEBUG_LVL >= 4
      println(f, "}")
      close(f)
    end
end

"""
Process an array of expressions.
We know that the first array of expressions we will find is for the lambda body.
top_level_number starts out 0 and if we find it to be 0 then we know that we're processing the array of expr for the body
and so we keep track of the index into body so that we can number the statements in the basic blocks by this top level number.
Recursively process each element of the array of expressions.
"""
function from_exprs(ast::Array{Any,1}, depth, state, callback, cbdata)
  # sequence of expressions
  # ast = [ expr, ... ]
  local len = length(ast)
  top_level = (state.top_level_number == 0)
  for i = 1:len
    if top_level
        state.top_level_number = i
        @dprintln(2,"Processing top-level ast #",i," depth=",depth)
    else
        @dprintln(2,"Processing ast #",i," depth=",depth)
    end
    @dprintln(3,"ast[", i, "] = ", ast[i])
    from_expr(ast[i], depth, state, top_level, callback, cbdata)
  end
  nothing
end

"""
For a given basic block "cur_bb", replace one of its successors "orig_succ" with a different successor "new_succ".
"""
function replaceSucc(cur_bb :: BasicBlock, orig_succ :: BasicBlock, new_succ :: BasicBlock)
  delete!(cur_bb.succs, orig_succ)   # delete the original successor from the set of successors
  push!(cur_bb.succs, new_succ)      # add the new successor to the set of successors

  # If we previously fell through to orig_succ then now we fallthrough to new_succ.
  if cur_bb.fallthrough_succ == orig_succ
    cur_bb.fallthrough_succ = new_succ
  else
    # If we didn't fall through then there must be a GotoNode or :gotoifnot Expr at the end of the block for 
    # which we need to change the label in that AST node again from orig_succ to new_succ.
    changeEndingLabel(cur_bb, orig_succ, new_succ)
  end
end

"""
Process a basic block and add its successors to the set of reachable blocks
if it isn't already there.  If it is freshly added then recurse to adds its successors.
"""
function findReachable(reachable, cur :: Int, bbs :: Dict{Int,BasicBlock})
  cur_bb = bbs[cur]

  for i in cur_bb.succs
    if !in(i.label, reachable)
      push!(reachable, i.label)
      findReachable(reachable, i.label, bbs)
    end
  end
end

"""
This function simplifies the dict of basic blocks "bbs".
One such simplification that is necessary for depth first numbering not to fail is the removal of dead blocks.
Other simplifications can be seen commented out below and while they may make the graph nicer to look at they
don't really add anything in terms of functionality.
"""
function removeUselessBlocks(bbs :: Dict{Int,BasicBlock}, opt)
  @dprintln(3, "removeUselessBlocks bbs = ", bbs, " opt = ", opt)
  found_change = opt

  # Eliminate dead blocks by finding the set of reachable blocks and eliminating the others.
  reachable = Set([-1])
  findReachable(reachable, -1, bbs)

  for i in bbs
    label = i[1]
    bb    = i[2]

    # Dead blocks.
    if !in(label, reachable)
      # Dead blocks can point to live ones so eliminate those useless back-edges.
      for j in bb.succs
        delete!(j.preds, bb)
      end

      @dprintln(3,"Removing dead block. ", bb)
      delete!(bbs, label)
    end
  end

  # Merge blocks if they have the pattern
  # stmt
  # goto N
  # N:
  # stmt
  while found_change
    found_change = false

    # For each basic block.
    for i in bbs
      bb = i[2]
      # If a basic block has only one successor then either it is from a fallthrough or
      # from a GotoNode.  If there is no fallthrough then it has to be a goto.
      # If there is no other "goto N" in the code, in other words, block N has only one predecessor
      # then we can eliminate the goto and the label.
      if length(bb.succs) == 1 && bb.fallthrough_succ == nothing 
          succ = first(bb.succs)
          if succ.label != CFG_EXIT_BLOCK && length(succ.preds) == 1
              @dprintln(3, "Eliminating basic block ", succ.label, " via the \"goto N; N:\" pattern.")
              if !isempty(bb.statements)
                  @dprintln(3, "Last BB statements = ", bb.statements[end])
              end
              assert(typeof(bb.statements[end].expr) == GotoNode)
              bb.succs = succ.succs
              bb.fallthrough_succ = succ.fallthrough_succ
              bb.statements = [bb.statements[1:end-1]; succ.statements[1:end]]
              for change_succ in bb.succs
                  delete!(change_succ.preds, succ)
                  push!(change_succ.preds, bb)
              end
              delete!(bbs, succ.label)

              found_change = true
              break
          end
      end
    end
  end

if false
  while found_change
    found_change = false

    for i in bbs
      bb = i[2]
#      # eliminate basic blocks with only one successor and no statements.
#      if length(bb.succs) == 1 && length(bb.statements) == 0
#        succ = first(bb.succs)
#        if succ.label != CFG_EXIT_BLOCK
#          delete!(succ.preds, bb)
#
#          for j in bb.preds
#            replaceSucc(j, bb, succ)
#            push!(succ.preds, j)
#          end
#
#          @dprintln(3,"Removing block with no statements and one successor. ", bb)
#          delete!(bbs, i[1])
#          found_change = true
#        end
#      elseif length(bb.preds) == 1 && length(bb.succs) == 1
#        pred = first(bb.preds)
#        succ = first(bb.succs)
#        if length(pred.succs) == 1 && succ.label != CFG_EXIT_BLOCK
#            replaceSucc(pred, bb, succ) 
#            delete!(succ.preds, bb)
#            push!(succ.preds, pred)
#            append!(pred.statements, bb.statements)
#            @dprintln(3,"Removing block with only one predecessor and successor. ", bb)
#            delete!(bbs, i[1])
#            found_change = true
#        end
#      elseif length(bb.preds) == 0 && bb.label != CFG_ENTRY_BLOCK
    end
  end
end
end

"""
A default callback that handles no extra AST node types.
"""
function not_handled(a,b)
  nothing
end

"""
The main entry point to construct a control-flow graph.
"""
function from_lambda(lambda::LambdaInfo; opt=true)
  @dprintln(3,"from_lambda for LambdaInfo")
  body = CompilerTools.LambdaHandling.getBody(lambda)
  from_expr(body, not_handled, nothing, opt)
end

function from_lambda(body::Expr; opt=true)
  @dprintln(3,"from_lambda for LambdaVarInfo and body")
  from_expr(body, not_handled, nothing, opt)
end

"""
Another entry point to construct a control-flow graph but one that allows you to pass a callback and some opaque object
so that non-standard node types can be processed.
"""
function from_expr(ast::Any, callback, cbdata, opt)
  @dprintln(2,"from_expr Body")
  @dprintln(3,ast)
  live_res = expr_state()
  # Recursively process the AST.
  from_expr(ast, 1, live_res, false, callback, cbdata)
  # Connect the active basic block at the end of the recursive processing with the final implicit basic block (-2).
  connect_finish(live_res)
# I simplifed removeUselessBlocks to just get rid of dead blocks (i.e., no predecessor)
  @dprintln(3,"before removeUselessBlocks ", length(live_res.basic_blocks), " ", live_res.basic_blocks)
  removeUselessBlocks(live_res.basic_blocks, opt)
  @dprintln(3,"after removeUselessBlocks ", length(live_res.basic_blocks), " ", live_res.basic_blocks)

  dfn = compute_dfn(live_res.basic_blocks)   # Compute the block depth first numbering.
  @dprintln(3,"dfn = ", dfn)
  ret = CFG(live_res.basic_blocks, dfn)      # Create the CFG object to be returned as the dictionary of label to basic blocks and the depth first numbering.
  @dprintln(2,"Dumping basic block info from_expr.")
  dump_bb(ret)
  return ret
end

"""
Process LabelNode for CFG construction.
"""
function from_label(label, state, callback, cbdata)
    @dprintln(2,"LabelNode: ", label)
    # If a basic block object has not already been created for the basic block started by this LabelNode AST node then create one.
    if !haskey(state.basic_blocks,label)
        state.basic_blocks[label] = BasicBlock(label)
    end
    # Create the fallthrough connection between the previous basic block (still in cur_bb) and the new basic block correspondingt to this LabelNode.
    connect(state.cur_bb, state.basic_blocks[label], true)
    # Set the current basic block to the one corresponding to this LabelNode.
    state.cur_bb = state.basic_blocks[label] 
    nothing
end

"""
Process a GotoNode for CFG construction.
"""
function from_goto(label, state, callback, cbdata)
    @dprintln(2,"GotoNode: ", label)
    # If a basic block object has not already been created for the basic block target of the goto then create one.
    if !haskey(state.basic_blocks,label)
        state.basic_blocks[label] = BasicBlock(label)
    end
    # Create a non-fallthrough connection between the current basic block and target of the goto.
    connect(state.cur_bb, state.basic_blocks[label], false)
    # Indicate that we are now not in any basic block.
    state.cur_bb = nothing
    # The next statement should be a label so cur_bb will be set there.
    nothing
end

"""
Process a :return Expr for CFG construction.
"""
function from_return(args, depth, state, callback, cbdata)
    @dprintln(2,"Expr return: ")
    from_exprs(args, depth, state, callback, cbdata)
    # Connect this basic block to the finish pseudo-basic block.
    connect(state.cur_bb, state.basic_blocks[CFG_EXIT_BLOCK], false)
    # Indicate that we are now not in any basic block.
    state.cur_bb = nothing
    nothing
end

"""
Process a :gotoifnot Expr not for CFG construction.
"""
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

    # Connect the current basic block to the the fall-through section with the implied (negative) label.
    connect(state.cur_bb, state.basic_blocks[implied], true)
    # Connect the current basic block to the explicit label target in the else case.
    connect(state.cur_bb, state.basic_blocks[else_label], false)

    # The new current basic block is the fall-through section.
    state.cur_bb = state.basic_blocks[implied]
    nothing
end

"""
The main routine that switches on all the various AST node types.
The internal nodes of the AST are of type Expr with various different Expr.head field values such as :lambda, :body, :block, etc.
The leaf nodes of the AST all have different types.
"""
function from_expr(ast::LambdaInfo, depth, state, top_level, callback, cbdata)
    return nothing
end

function from_expr(ast::Any, depth, state, top_level, callback, cbdata)
    @dprintln(2,"from_expr depth=",depth," ", " asttyp = ", typeof(ast))

    handled = callback(ast, cbdata)
    if handled != nothing
        addStatement(top_level, state, ast)
        if length(handled) > 0
            @dprintln(3,"Processing expression from callback for ", ast)
            @dprintln(3,handled)
            from_exprs(handled, depth+1, state, callback, cbdata)
            @dprintln(3,"Done processing expression from callback.")
        end
        return nothing
    end

    from_expr_helper(ast, depth, state, top_level, callback, cbdata)

    return nothing
end

function from_expr_helper(ast::Expr, depth, state, top_level, callback, cbdata)
    addStatement(top_level, state, ast)

    @dprint(2,"Expr ")
    local head = ast.head
    local args = ast.args
    local typ  = ast.typ
    @dprintln(2,head, " ", args)
    if head == :lambda
        assert(length(args) == 3)
        from_expr(args[3], depth, state, false, callback, cbdata)
    elseif head == :body
        from_exprs(args, depth+1, state, callback, cbdata)
    elseif head == :return
        from_return(args,depth,state, callback, cbdata)
    elseif head == :gotoifnot
        from_if(args,depth,state, callback, cbdata)
    end
end

function from_expr_helper(ast::LabelNode, depth, state, top_level, callback, cbdata)
    from_label(ast.label, state, callback, cbdata)
end

function from_expr_helper(ast::GotoNode, depth, state, top_level, callback, cbdata)
    addStatement(top_level, state, ast)
    from_goto(ast.label, state, callback, cbdata)
end

function from_expr_helper(ast::ANY, depth, state, top_level, callback, cbdata)
    addStatement(top_level, state, ast)
end

"""
Compute the dominators of the CFG.
"""
function compute_dominators(bl :: CFG)
  # Compute dominators.
  # https://en.wikipedia.org/wiki/Dominator_(graph_theory)
  # The above webpage describes what a dominator is and a simple way to calculate them.
  # Their data-flow equations inspired the following concrete implementation.

  # Get the depth-first numering for the CFG.
  bbs_df_order = bl.depth_first_numbering
  # Get the number of basic blocks.
  num_bb = length(bl.basic_blocks)
  assert(num_bb == length(bbs_df_order))

  all_set = Set()
  for i in collect(keys(bl.basic_blocks))
      push!(all_set, i)
  end
  dom_dict = Dict{Int,Set}()
  for i in collect(keys(bl.basic_blocks))
      if i == CFG_ENTRY_BLOCK
          dom_dict[i] = Set(CFG_ENTRY_BLOCK)
      else
          dom_dict[i] = deepcopy(all_set)
      end
  end

  count = 0;
  change_found = true
  while(change_found)
      @dprintln(3,"compute_dom_loops: dom_dict = ", dom_dict)

      count = count + 1
      if count > 1000
          throw(string("Probable infinite loop in compute_dominators."))
      end

      change_found = false

      for i = 1:num_bb
          bb_index = bbs_df_order[i]
          bb = bl.basic_blocks[bb_index]

          if bb_index != CFG_ENTRY_BLOCK
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

  return dom_dict
end

"""
Compute the inverse dominators of the CFG.
"""
function compute_inverse_dominators(bl :: CFG)
  # Compute inverse dominators.
  # https://en.wikipedia.org/wiki/Dominator_(graph_theory)
  # The above webpage describes what a dominator is and a simple way to calculate them.
  # Their data-flow equations inspired the following concrete implementation.

  # Get the depth-first numering for the CFG.
  bbs_df_order = bl.depth_first_numbering
  # Get the number of basic blocks.
  num_bb = length(bl.basic_blocks)
  assert(num_bb == length(bbs_df_order))

  all_set = Set()
  for i in collect(keys(bl.basic_blocks))
      push!(all_set, i)
  end
  dom_dict = Dict{Int,Set}()
  for i in collect(keys(bl.basic_blocks))
      if i == CFG_EXIT_BLOCK
          dom_dict[i] = Set(CFG_EXIT_BLOCK)
      else
          dom_dict[i] = deepcopy(all_set)
      end
  end

  count = 0;
  change_found = true
  while(change_found)
      @dprintln(3,"compute_dom_loops: dom_dict = ", dom_dict)

      count = count + 1
      if count > 1000
          throw(string("Probable infinite loop in compute_inverse_dominators."))
      end

      change_found = false

      for i = num_bb:-1:1
          bb_index = bbs_df_order[i]
          bb = bl.basic_blocks[bb_index]

          if bb_index != CFG_EXIT_BLOCK
              if length(bb.succs) != 0
                  succ_array = collect(bb.succs)
                  vb = deepcopy(dom_dict[succ_array[1].label])
                  for j = 2:length(succ_array)
                      vb = intersect(vb, dom_dict[succ_array[j].label])
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

  return dom_dict
end

end

