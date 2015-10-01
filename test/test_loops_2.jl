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
cfg_2 = CompilerTools.CFGs.from_ast(ast_lv_2) :: CompilerTools.CFGs.CFG

#CompilerTools.Loops.set_debug_level(3)

all_loops = CompilerTools.Loops.compute_dom_loops(cfg_2)

@test (length(all_loops.loops) == 4)
@test (CompilerTools.Loops.isInLoop(all_loops, 8) == false)
@test (CompilerTools.Loops.isInLoop(all_loops, 16) == true)