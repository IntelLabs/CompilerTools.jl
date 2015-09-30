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
