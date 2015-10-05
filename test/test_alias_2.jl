using CompilerTools
using Base.Test

## Tests for CompilerTools.AliasAnalysis

function test_loops(x::Int, y::Int, z::Int, s::Int)
         A = rand(x, y)
         D_arr = rand(x, y)
	 C = rand(x,y)
	 B = D_arr

	 for i = 1:y
	      if( i%2 == 0 )
	      	  for j = 1:z
		      D_arr[i,j] /= 2
		  end
	      end
	  end
	  
	  E = B
	  if( s > 0 )
	      E = A
	  end
         return E

end

ast = code_typed(test_loops, (Int,Int,Int,Int))[1]
#cfg_2 = CompilerTools.CFGs.from_ast(ast) :: CompilerTools.CFGs.CFG

CompilerTools.AliasAnalysis.set_debug_level(3)
function cb_func(a,b)
  nothing
end
lives = CompilerTools.LivenessAnalysis.from_expr(ast, cb_func, nothing )

function cb_func1(a,b,c)
  nothing
end

handled = CompilerTools.AliasAnalysis.analyze_lambda(ast, lives, cb_func1, nothing)
println(handled)
@test (in(:C, handled))
@test (in(:E, handled) == false)
@test (in(:B, handled) == false)
@test (in(:D_arr, handled) == false)
@test (in(:A, handled) == false)

