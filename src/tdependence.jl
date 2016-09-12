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

using CompilerTools
using CompilerTools.LivenessAnalysis
using CompilerTools.Helper

function computeDependencies(bl :: CompilerTools.LivenessAnalysis.BlockLiveness)
    change = true

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

    while change
        change = false

        for ventry in ret
            vdef    = ventry[1]
            vdepset = ventry[2]

            new_depset = vdepset

            for dep in vdepset
                if haskey(ret, dep)
                    new_depset = union(new_depset, ret[dep])
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

end
