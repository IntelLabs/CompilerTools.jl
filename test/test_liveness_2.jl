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
@test length(lives_2.basic_blocks[lives_2.cfg.basic_blocks[6]].def) == 6
@test length(lives_2.basic_blocks[lives_2.cfg.basic_blocks[6]].use) == 3

@test length(lives_2.basic_blocks[lives_2.cfg.basic_blocks[14]].live_in) == 13
@test length(lives_2.basic_blocks[lives_2.cfg.basic_blocks[14]].live_out) == 13
@test length(lives_2.basic_blocks[lives_2.cfg.basic_blocks[14]].def) == 8
@test length(lives_2.basic_blocks[lives_2.cfg.basic_blocks[14]].use) == 6

@test length(lives_2.cfg.basic_blocks) == 26