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

function test_loops(a::Int64)
	 b = a * 2
	 c = b + 1
	 d = 0
	 if(a>10)
	   for i = 1:a
	     c *= 2
	     for j = 1:10
	     	 d += c*j
	     end
	   end
	 else
	   for i = 1:10
	     c *= 2
	     for j = 1:10
	     	 d += c*j
	     end
	   end
	  end
end

ast_lv_2 = code_typed(test_loops, (Int64,))[1]
cfg_2 = CompilerTools.CFGs.from_lambda(ast_lv_2) :: CompilerTools.CFGs.CFG

#CompilerTools.Loops.set_debug_level(3)

all_loops = CompilerTools.Loops.compute_dom_loops(cfg_2)

@test (length(all_loops.loops) == 4)
# Need to think about better tests that don't depend on absolute basic block numbers that can change with Julia versions.
#@test (CompilerTools.Loops.isInLoop(all_loops, 8) == false)
#@test (CompilerTools.Loops.isInLoop(all_loops, 16) == true)
