module Loops

using CompilerTools

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

import Base.show

export DomLoops, Loop

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
    loops    :: Array{Loop,1}
end

function findLoopInvariants(l :: Loop, 
                            udinfo :: Dict{CompilerTools.LivenessAnalysis.BasicBlock,CompilerTools.UDChains.UDInfo}, 
                            bl :: CompilerTools.LivenessAnalysis.BlockLiveness)
    all_uses = Set{Symbol}()

    dprintln(3,l.members)
    dprintln(3,collect(keys(bl.basic_blocks)))
    dprintln(3,bl)

    # Accumulate all uses in the loop.
    for i in l.members
        dprintln(3,"i = ", i)
        bb = bl.basic_blocks[i]  # get the basic block from its index
        all_uses = union(all_uses, bb.use)
    end

    dprintln(3, "all_uses = ", all_uses)

    # Eliminate uses that have a definition in the loop.
    for i in l.members
        dprintln(3,"i = ", i)
        bb = bl.basic_blocks[i]  # get the basic block from its index
        bb_ud = udinfo[bb]
        dprintln(3, bb_ud)
        # Get all the inputs to this block.
        for j in bb_ud.live_in
            dprintln(3, "symbol in block live_in = ", j[1])
            # If one of those inputs is used in this basic block of the loop.
            if in(j[1], all_uses)
                dprintln(3, "symbol in all_uses")
                for k in j[2]
                    if k == nothing
                        continue
                    end
                    dprintln(3, "this block = ", k.label)
                    if in(k.label, l.members)
                        temp_set = Set{Symbol}()
                        push!(temp_set, j[1])
                        dprintln(3, "this block belongs to members all_uses = ", all_uses, " type = ", typeof(all_uses), " type j[1] = ", typeof(j[1]), " temp set = ", temp_set)
                        all_uses = setdiff(all_uses, temp_set)
                        break
                    end
                end
            end
        end
    end

    return all_uses
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

function compute_dom_loops(bl::CompilerTools.LivenessAnalysis.BlockLiveness)
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

end
