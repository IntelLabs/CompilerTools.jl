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

using CompilerTools
using Base.Test

## Tests for CompilerTools.LivenessAnalysis

function test_liveness_2(x::Int64, y::Int64, z::Int64)
	 A = random(x, y)
	 B = random(y, z)
	 C = zeros(x, z)
	 for i = 1:x
	     for j = 1:y
	     	 A[i,j] += 1;
	     end
	     for j = 1:z
	     	 for k = 1:y
		     C[i,j] += A[i,k] * B[k,j] + 1
		 end
	     end
	  end
end

ast_lv_2 = code_lowered(test_liveness_2, (Int64,Int64,Int64))[1]
cfg_2 = CompilerTools.CFGs.from_ast(ast_lv_2) :: CompilerTools.CFGs.CFG

#CompilerTools.Loops.set_debug_level(3)

all_loops = CompilerTools.Loops.compute_dom_loops(cfg_2)

#println((all_loops.dom_dict))
@test (length(all_loops.loops) == 4)
@test (CompilerTools.Loops.isInLoop(all_loops, -1) == false)
@test (CompilerTools.Loops.isInLoop(all_loops, 6) == true)
