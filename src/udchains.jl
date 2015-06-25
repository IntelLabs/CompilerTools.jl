module UDChains

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

type UDInfo
    live_in  :: Dict{Symbol,Set}
    live_out :: Dict{Symbol,Set}

    function UDInfo()
        new(Dict{Symbol,Set}(), Dict{Symbol,Set}())
    end
end

function getOrCreate(live :: Dict{Symbol, Set}, s :: Symbol)
    if !haskey(live, s)
        live[s] = Set()
    end
    return live[s]
end

function getOrCreate(udchains :: Dict{CompilerTools.LivenessAnalysis.BasicBlock,UDInfo} , bb :: CompilerTools.LivenessAnalysis.BasicBlock)
    if !haskey(udchains, bb)
        udchains[bb] = UDInfo()
    end
    return udchains[bb]
end

function printSet(level, s)
    for j in s
        if typeof(j) == CompilerTools.LivenessAnalysis.BasicBlock
            dprint(level, " ", j.label)
        else
            dprint(level, " ", j)
        end
    end
end

function printLabels(level, dict)
    for i in dict
       dprint(level, "\tSymbol: ", i[1], " From:")
       printSet(level, i[2])
       dprintln(level,"")
    end
end

function printUDInfo(level, ud)
    for i in ud
        dprintln(level, i[1].label, " Live In:")
        printLabels(level, i[2].live_in)
        dprintln(level, i[1].label, " Live Out:")
        printLabels(level, i[2].live_out)
    end
end

function getUDChains(bl :: CompilerTools.LivenessAnalysis.BlockLiveness)
    udchains = Dict{CompilerTools.LivenessAnalysis.BasicBlock,UDInfo}()

    dprintln(3,"getUDChains: bl = ", bl)

    body_order = CompilerTools.LivenessAnalysis.getBbBodyOrder(bl)
    changed = true
    # Iterate until nothing changes.
    while changed
        dprintln(3,"getUDChains: main loop")
        changed = false
        # For each basic block from beginning to end.
        for i = 1:length(body_order)
            bb = bl.basic_blocks[body_order[i]]
            # Get the UDChain info for this basic block.
            udinfo = getOrCreate(udchains, bb)
            dprintln(3,"getUDChains: bb = ", bb, " udinfo = ", udinfo)

            for li in bb.live_in
                # Get the current set of blocks from which this symbol could be defined and reach here.
                li_set = getOrCreate(udinfo.live_in, li)
                dprint(3,"getUDChains: li = ", li, " li_set = ")
                printSet(3,li_set)
                dprintln(3,"")
 
                if isempty(bb.preds)
                    dprintln(3,"getUDChains: no preds")
                    # Must be the starting block.
                    # Use "nothing" to represent the parameter set.
                    if !in(nothing, li_set)
                        dprintln(3,"getUDChains: added nothing to li_set")
                        push!(li_set, nothing)
                        changed = true
                    end
                else
                    # Non-starting block.
                    for pred in bb.preds
                        pred_udinfo = getOrCreate(udchains, pred)
                        pred_lo_set = getOrCreate(pred_udinfo.live_out, li)
                        #dprint(3,"getUDChains: pred = ", pred.label, " pred_udinfo = ", pred_udinfo, " pred_lo_set = ", pred_lo_set)
                        dprint(3,"getUDChains: pred = ", pred.label, " pred_lo_set = ", pred_lo_set)
                        printSet(3,li_set)
                        dprintln(3,"")
                        for pred_lo in pred_lo_set
                            if !in(pred_lo, li_set)
                                push!(li_set, pred_lo)
                                changed = true
                                dprintln(3,"getUDChains: added ", pred_lo, " to li_set = ", li_set)
                            end
                        end
                    end
                end
            end

            # For each symbol live_out of this block.
            for lo in bb.live_out
                # Get the current set of blocks from which this symbol could be defined and reach here.
                lo_set = getOrCreate(udinfo.live_out, lo)
                dprint(3,"getUDChains: lo = ", lo, " lo_set = ")
                printSet(3,lo_set)
                dprintln(3,"")

                # If this live out was defined in this block...
                if in(lo, bb.def)
                    dprintln(3,"getUDChains: lo def in block")
                    # ... then add this block to udchain for this symbol.
                    if !in(bb, lo_set)
                        dprintln(3,"getUDChains: adding bb to lo_set")
                        push!(lo_set, bb)
                        changed = true
                    end 
                else
                    # Not defined in this block so must be live_in.
                    li_set = getOrCreate(udinfo.live_in, lo)
                    dprintln(3,"getUDChains: not def in block so using li_set = ", li_set)
                    for li_bb in li_set
                        if !in(li_bb, lo_set)
                            dprintln(3,"getUDChains: adding ", typeof(li_bb)==CompilerTools.LivenessAnalysis.BasicBlock ? li_bb.label : li_bb, " to lo_set")
                            push!(lo_set, li_bb)
                            changed = true
                        end 
                    end
                end
            end
        end 
    end

    return udchains
end

end
