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

module TransitiveDependence

import ..DebugMsg
DebugMsg.init()

using CompilerTools
using CompilerTools.Helper
using CompilerTools.AstWalker
using CompilerTools.LambdaHandling
using CompilerTools.LivenessAnalysis
using CompilerTools.Helper

import Base.show

function show(io::IO, d :: Dict{LHSVar, Set{LHSVar}})
    for ventry in d
        vdef    = ventry[1]
        vdepset = ventry[2]
        println(vdef, " => ", vdepset)
    end
end

type cddata
    ret :: Dict{LHSVar, Set{LHSVar}}
    defs
    uses
    cb
    data
end

type CallbackResult
    ret :: Dict{LHSVar, Set{LHSVar}}
    defs
    uses
    read_exprs
    write_exprs
end

function mergeDepSet(merge_into :: Dict{LHSVar, Set{LHSVar}}, 
                     merge_from :: Dict{LHSVar, Set{LHSVar}})
    for cbitem in merge_from
        vdef    = cbitem[1]
        vdefset = cbitem[2]

        if haskey(merge_into, vdef)
            cur_set = merge_into[vdef]
        else
            cur_set = Set{LHSVar}()
        end

        # Compute the new immediate dependency set for this variable.
        cur_set = union(cur_set, vdefset)
        # Remember the new immediate dependency set for this variable.
        merge_into[vdef] = cur_set
    end

    return merge_into
end

function finishStatement(data :: cddata)
    for cur_def in data.defs
        # Start with an empty use set if we haven't processed a statement that defines this variable before.
        # Else, start with the immediate dependency set as previously computed for this variable.
        if haskey(data.ret, cur_def)
            cur_set = data.ret[cur_def]
        else
            cur_set = Set{LHSVar}()
        end

        # Compute the new immediate dependency set for this variable.
        cur_set = union(cur_set, data.uses)
        # Remember the new immediate dependency set for this variable.
        data.ret[cur_def] = cur_set
    end
    data.defs = Set{LHSVar}()
    data.uses = Set{LHSVar}()
end

function cdwalk(x :: ANY, data :: cddata, top_level_number, is_top_level, read)
    if is_top_level
        finishStatement(data)
    end

    if data.cb != nothing
        cbres = data.cb(x, data.data)
        if cbres != nothing
            assert(isa(cbres, CallbackResult))
            mergeDepSet(data.ret, cbres.ret)
            data.uses = union(data.uses, cbres.uses)
            data.defs = union(data.defs, cbres.defs)
            for r in cbres.read_exprs
                CompilerTools.AstWalker.from_expr(r, 1, cdwalk, data, 1, false, true)
            end
            for w in cbres.write_exprs
                CompilerTools.AstWalker.from_expr(w, 1, cdwalk, data, 1, false, false)
            end
            return x
        end
    end

    if isa(x, RHSVar)
        lhsvar = toLHSVar(x)
        if read
            push!(data.uses, lhsvar)
        else
            push!(data.defs, lhsvar)
        end        
    end

    return CompilerTools.AstWalker.ASTWALK_RECURSE
end

function computeDependenciesAST(body :: ANY, callback=not_handled, cbdata :: ANY=nothing)
    data = cddata(Dict{LHSVar,Set{LHSVar}}(), Set{LHSVar}(), Set{LHSVar}(), callback, cbdata)
    AstWalk(body, cdwalk, data)
    finishStatement(data)
    @dprintln(3, "Before transitive in computeDependenciesAST")
    @dprintln(3, data.ret)
    return transitive(data.ret)
end

function transitive(ret :: Dict{LHSVar, Set{LHSVar}})
    change = true

    while change
        change = false

        for ventry in ret
            vdef    = ventry[1]
            vdepset = ventry[2]

            new_depset = vdepset

            for dep in vdepset
                if haskey(ret, dep)
                    new_depset = union(new_depset, ret[dep])
                    @dprintln(3, vdef, " after merging ", dep, " => ", new_depset)
                end
            end

            if new_depset != vdepset
                change = true
                ret[vdef] = new_depset
            end
        end
    end

    return ret
end

function computeDependencies(bl :: CompilerTools.LivenessAnalysis.BlockLiveness)
    @dprintln(3,"computeDependencies bl = ", bl)

    ret = Dict{LHSVar, Set{LHSVar}}()

    # Make one pass over all the basic blocks.
    for bbentry in bl.basic_blocks
        bb = bbentry[2]

        # For each statement in every basic block.
        for stmt in bb.statements
            # For each variable defined by this statement.
            for cur_def in stmt.def
                # Start with an empty use set if we haven't processed a statement that defines this variable before.
                # Else, start with the immediate dependency set as previously computed for this variable.
                if haskey(ret, cur_def)
                    cur_set = ret[cur_def]
                else
                    cur_set = Set{LHSVar}()
                end

                # Compute the new immediate dependency set for this variable.
                cur_set = union(cur_set, stmt.use)
                # Remember the new immediate dependency set for this variable.
                ret[cur_def] = cur_set
            end
        end
    end        

    @dprintln(3, "Initial vdepset based on statements.")
    @dprintln(3, ret)

    return transitive(ret)
end

end
