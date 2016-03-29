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

module Loops

import ..DebugMsg
DebugMsg.init()

using CompilerTools
import Base.show
export DomLoops, Loop

"""
A type to hold information about a loop.
A loop has a "head" that dominates all the other blocks in the loop.
A loop has a back_edge which is a block that has "head" as one of its successors.
It also contains "members" which is a set of basic block labels of all the basic blocks that are a part of this loop.
"""
type Loop
    head :: Int
    back_edge :: Int
    members :: Set{Int}

    function Loop(h :: Int, b :: Int, m :: Set{Int})
        new(h, b, m)
    end
end

"""
A type that holds information about which basic blocks dominate which other blocks.
It also contains an array "loops" of all the loops discovered within the function.
The same basic block may occur as a member in multiple loop entries if those loops are nested.
This module doesn't currently help identify these nesting levels but by looking at loop members it is easy enough to figure out.
"""
type DomLoops
    dom_dict :: Dict{Int,Set}
    loops    :: Array{Loop,1}
end

function getPreLoopBlock(l :: Loop, bl :: CompilerTools.CFGs.CFG)
    head_bb = bl.basic_blocks[l.head]
    return setdiff(map(x -> x.label, head_bb.preds), l.members)
end

function getPostLoopBlock(l :: Loop, bl :: CompilerTools.CFGs.CFG)
    back_edge_bb = bl.basic_blocks[l.back_edge]
    return setdiff(map(x -> x.label, back_edge_bb.succs), l.members)
end

function insertNewBlockBeforeLoop(l :: Loop, bl :: CompilerTools.CFGs.CFG, stmts :: Array{Any,1})
    @dprintln(3, "insertNewBlockBeforeLoop l = ", l, " bl = ", bl, " stmts = ", stmts)
    new_bb, new_goto_stmt = CompilerTools.CFGs.insertBefore(bl, l.head, true, l.back_edge)
    @dprintln(3, "new_bb = ", new_bb, " new_goto_stmt = ", new_goto_stmt.expr)
    for stmt in stmts
        CompilerTools.CFGs.addStatementToEndOfBlock(bl, new_bb, stmt)
    end
    if new_goto_stmt != nothing
        push!(new_bb.statements, new_goto_stmt)
    end
    return new_bb
end

"""
Takes a DomLoops object containing loop information about the function.
Returns true if the given basic block label "bb" is in some loop in the function.
"""
function isInLoop(dl :: DomLoops, bb :: Int)
    for i in dl.loops
        if in(bb, i.members)
            return true
        end
    end

    return false
end

"""
Finds those computations within a loop that are iteration invariant.
Takes as input:
   l - the Loop to find invariants in
   udinfo - UDChains (use-definition chains) for the basic blocks of the function.
   bl - LivenessAnalysis.BlockLiveness with liveness information for variables within the function.
"""
function findLoopInvariants(l :: Loop, 
                            udinfo :: Dict{CompilerTools.LivenessAnalysis.BasicBlock,CompilerTools.UDChains.UDInfo}, 
                            bl :: CompilerTools.LivenessAnalysis.BlockLiveness)
    all_uses = Set{Symbol}()

    @dprintln(3,l.members)
    @dprintln(3,collect(keys(bl.basic_blocks)))
    @dprintln(3,bl)

    # Accumulate a set of all variables used in the loop.
    for i in l.members
        @dprintln(3,"i = ", i)
        bb = bl.basic_blocks[i]  # get the basic block from its index
        all_uses = union(all_uses, bb.use)
    end

    @dprintln(3, "all_uses = ", all_uses)

    # Eliminate all variable usages in "all_uses" that have a definition in the loop.
    for i in l.members
        @dprintln(3,"i = ", i)
        bb = bl.basic_blocks[i]  # get the basic block from its index
        bb_ud = udinfo[bb]
        @dprintln(3, bb_ud)
        # Get all the inputs to this block.
        for j in bb_ud.live_in
            @dprintln(3, "symbol in block live_in = ", j[1])
            # If one of those inputs is used in this basic block of the loop.
            if in(j[1], all_uses)
                @dprintln(3, "symbol in all_uses")
                for k in j[2]
                    if k == nothing
                        continue
                    end
                    @dprintln(3, "this block = ", k.label)
                    if in(k.label, l.members)
                        temp_set = Set{Symbol}()
                        push!(temp_set, j[1])
                        @dprintln(3, "this block belongs to members all_uses = ", all_uses, " type = ", typeof(all_uses), " type j[1] = ", typeof(j[1]), " temp set = ", temp_set)
                        all_uses = setdiff(all_uses, temp_set)
                        break
                    end
                end
            end
        end
    end

    # At this point, we have an initial seed for loop-invariant computation in a set of variables that are used in the loop but never defined anywhere in the loop.

    changed = true
    while(changed)
        # While we keep finding more loop invariant computations, keep iterating.
        changed = false
        @dprintln(0,"starting changed loop")
        non_invariant = Set()
        invariant     = Set()

        # Try to find calculations that depend only on constants or other loop invariant calculatings and put those in "invariant".
        for i in l.members
            bb = bl.basic_blocks[i]  # get the basic block from its index
            for stmt in bb.statements
                if !isempty(stmt.def)
                    # Compute symbols used in the statement that aren't invariant.
                    non_invariants = setdiff(stmt.use, all_uses)
                    @dprintln(0,"Def statement use = ", stmt.use, " all_uses = ", all_uses, " non_invariants = ", non_invariants, " stmt = ", stmt)
                    if isempty(non_invariants)
                        # def could be invariants if they aren't non_invariant elsewhere.
                        for def in stmt.def
                            if !in(def, non_invariant) && !in(def, all_uses)
                                push!(invariant, def)
                            end
                        end 
                    else
                        # def isn't invariant so remove from invariant if a prior statement that was invariant was added.
                        for def in stmt.def
                            if in(def, invariant)
                                delete!(invariant, def)
                            end
                            push!(non_invariant, def)
                        end 
                    end
                    @dprintln(0,"non_invariant set = ", non_invariant, " invariant set = ", invariant)
                end
            end
        end

        # If we found additional loop invariant calculations then add them to the set of invariant calculation in all_uses and indicate we found a change
        # so that the loop will continue searching for more.
        if !isempty(invariant)
            @dprintln(0,"Found some new invariants = ", invariant)
            changed = true
            all_uses = union(all_uses, invariant)
        end
    end

    return all_uses
end

"""
Add to the "members" of the loop being accumulated given "cur_bb" which is known to be a member of the loop.
"""
function flm_internal(cur_bb, members, bbs)
    # If we haven't previously added the current basic block to the member set.
    if !in(cur_bb, members)
        bb = bbs[cur_bb]
        # Add the BasicBlock object for cur_bb to the members set.
        push!(members, cur_bb)

        # Add all predecessors of the current block as loop members.
        for pred in bb.preds
            flm_internal(pred.label, members, bbs)
        end
    end
    members
end

"""
Find all the members of the loop as specified by the "head" basic block and the "back_edge" basic block.
Also takes the dictionary of labels to basic blocks.
Start with just the head of the loop as a member and then starts recursing with the back_edge using flm_internal.
"""
function findLoopMembers(head, back_edge, bbs)
    members = Set(head)
    flm_internal(back_edge, members, bbs)
end

"""
Find the loops in a CFGs.CFG in "bl".
"""
function compute_dom_loops(bl :: CompilerTools.CFGs.CFG)
    # Get the depth-first numering for the CFG.
    bbs_df_order = bl.depth_first_numbering
    # Get the number of basic blocks.
    num_bb = length(bl.basic_blocks)
    assert(num_bb == length(bbs_df_order))

    dom_dict = CompilerTools.CFGs.compute_dominators(bl)

    loops = Loop[]

    # Find the loop in the function.
    for i = 1:num_bb
        # For each basic block ...
        bb_index = bbs_df_order[i]
        bb = bl.basic_blocks[bb_index]
        succ_array = collect(bb.succs)
        for j in succ_array
            local succ_id = j.label
            # If one of the block's successors dominates the current basic block then we've found a loop.
            if in(succ_id, dom_dict[bb_index])
                # Identify the members of the loop.
                members = findLoopMembers(succ_id, bb_index, bl.basic_blocks)
                @dprintln(3,"loop members = ", members, " type = ", typeof(members))
                new_loop = Loop(succ_id, bb_index, members)
                @dprintln(3,"new_loop = ", new_loop, " type = ", typeof(new_loop))
                # Store the Loop information in the array of loops to be returned.
                push!(loops, new_loop)
            end
        end
    end

    DomLoops(dom_dict, loops)  # Return the dominator information and the array of loops found.
end

end
