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

function test_alias_1(x::Int64, y::Int64, z::Int64)
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

ast = code_typed(test_alias_1, (Int64,Int64,Int64,))[1]
linfo, body = lambdaToLambdaVarInfo(ast)
#println("ast = ", ast)
#println("linfo = ", linfo)

#cfg_2 = CompilerTools.CFGs.from_lambda(ast) :: CompilerTools.CFGs.CFG

#CompilerTools.AliasAnalysis.set_debug_level(3)
#CompilerTools.CFGs.set_debug_level(4)
#CompilerTools.LivenessAnalysis.set_debug_level(5)
#CompilerTools.LambdaHandling.set_debug_level(5)

lives = CompilerTools.LivenessAnalysis.from_lambda(linfo, body)
#println("lives = ")
#println(lives)
handled = CompilerTools.AliasAnalysis.from_lambda(linfo, body, lives)
handled = map(x -> lookupVariableName(x, linfo), handled)
#println("handled = ", handled)

@test (in(:A, handled))
@test (in(:D_arr, handled) == false)
@test (in(:B, handled) == false)
#TODO: C is not detected now.
#@test (in(:C, handled))
