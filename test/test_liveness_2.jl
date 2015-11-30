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
	 A = rand(x, y)
	 B = rand(y, z)
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

ast_lv_2 = code_typed(test_liveness_2, (Int64,Int64,Int64))[1]

#CompilerTools.LivenessAnalysis.set_debug_level(3)
function cb_func(a,b)
  nothing
end
lives_2 = CompilerTools.LivenessAnalysis.from_expr(ast_lv_2, cb_func, nothing )
#= 
println( length(lives_2.basic_blocks[lives_2.cfg.basic_blocks[6]].live_in))
println( length(lives_2.basic_blocks[lives_2.cfg.basic_blocks[6]].live_out))
println( length(lives_2.basic_blocks[lives_2.cfg.basic_blocks[6]].def))  
println( length(lives_2.basic_blocks[lives_2.cfg.basic_blocks[6]].use))

println( length(lives_2.basic_blocks[lives_2.cfg.basic_blocks[14]].live_in))
println( length(lives_2.basic_blocks[lives_2.cfg.basic_blocks[14]].live_out))
println( length(lives_2.basic_blocks[lives_2.cfg.basic_blocks[14]].def))
println( length(lives_2.basic_blocks[lives_2.cfg.basic_blocks[14]].use))
=#

@test length(lives_2.basic_blocks[lives_2.cfg.basic_blocks[6]].live_in) == 10
@test length(lives_2.basic_blocks[lives_2.cfg.basic_blocks[6]].live_out) == 10
#@test length(lives_2.basic_blocks[lives_2.cfg.basic_blocks[6]].def) == 6
#@test length(lives_2.basic_blocks[lives_2.cfg.basic_blocks[6]].use) == 3

@test length(lives_2.basic_blocks[lives_2.cfg.basic_blocks[14]].live_in) == 13
@test length(lives_2.basic_blocks[lives_2.cfg.basic_blocks[14]].live_out) == 13
#@test length(lives_2.basic_blocks[lives_2.cfg.basic_blocks[14]].def) == 8
#@test length(lives_2.basic_blocks[lives_2.cfg.basic_blocks[14]].use) == 6

@test length(lives_2.cfg.basic_blocks) == 26
