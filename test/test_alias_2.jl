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
using CompilerTools.LambdaHandling
using Base.Test

## Tests for CompilerTools.AliasAnalysis

function test_alias_2(x::Int, y::Int, z::Int, s::Int)
     A = rand(x, y)
     D_arr = rand(x, y)
     C = rand(x,y)
     B = D_arr

     for i = 1:x
          if( i%2 == 0 )
              for j = 1:y
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

ast = CompilerTools.Helper.LambdaInfo(test_alias_2, (Int,Int,Int,Int), code_typed(test_alias_2, (Int,Int,Int,Int))[1])
linfo, body = lambdaToLambdaVarInfo(ast)
#cfg_2 = CompilerTools.CFGs.from_lambda(ast) :: CompilerTools.CFGs.CFG

#CompilerTools.AliasAnalysis.set_debug_level(3)
lives = CompilerTools.LivenessAnalysis.from_lambda(linfo, body)
handled = CompilerTools.AliasAnalysis.from_lambda(linfo, body, lives)
handled = map(x -> lookupVariableName(x, linfo), handled)
#println(handled)
#@test (in(:C, handled))
@test (in(:E, handled) == false)
@test (in(:B, handled) == false)
#@test (in(:D_arr, handled) == false)
#@test (in(:A, handled) == false)

