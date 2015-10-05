using CompilerTools
using Base.Test

## Tests for CompilerTools.AliasAnalysis

function test_loops(x::Int64, y::Int64, z::Int64)
         A = rand(x, y)
         D_arr = rand(y, z)
         C = zeros(x, z)
	 B = D_arr

	 for i = 1:y
	      if( i%2 == 0 )
	      	  for j = 1:z
		      D_arr[i,j] /= 2
		  end
	      end
	  end

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

ast = code_typed(test_loops, (Int64,Int64,Int64,))[1]
#cfg_2 = CompilerTools.CFGs.from_ast(ast) :: CompilerTools.CFGs.CFG

#CompilerTools.AliasAnalysis.set_debug_level(3)
function cb_func(a,b)
  nothing
end
lives = CompilerTools.LivenessAnalysis.from_expr(ast, cb_func, nothing )

function cb_func1(a,b,c)
  nothing
end

handled = CompilerTools.AliasAnalysis.analyze_lambda(ast, lives, cb_func1, nothing)

@test (in(:A, handled))
#TODO: D is not detected now.
#@test (in(:D, handled))
