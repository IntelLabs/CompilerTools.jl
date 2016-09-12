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

function test_liveness_1(x::Int64, y::Int64, s::Int64)
    C1 = (x - 256.0) / s + 0.6
    C2 = (y - 256.0) / s + 0.8
    acc1 = 0.0
    acc2 = 0.0
    I2 = 0.0
    R2 = 0.0
    n = 0
    while (R2+I2 < 1.0) && (n < 512)
       acc1 = (acc2+acc2)*acc1+C1;
       acc2 = R2-I2+C2;
       R2 = acc2*acc2;
       I2 = acc1*acc1;
       n += 1;
    end
    return n;
end

ast_lv_1 = code_typed(test_liveness_1, (Int64,Int64,Int64))[1]
# cfg_lv_1 = CompilerTools.CFGs.from_ast(ast_lv_1) :: CompilerTools.CFGs.CFG

linfo, body = CompilerTools.LambdaHandling.lambdaToLambdaVarInfo(ast_lv_1)

#CompilerTools.LivenessAnalysis.set_debug_level(3)
#CompilerTools.LambdaHandling.set_debug_level(3)
lives_1 = CompilerTools.LivenessAnalysis.from_lambda(ast_lv_1)

# The AST changes too frequently to be testing anything but perhaps the starting block and even that is suspect.
@test length(lives_1.basic_blocks[lives_1.cfg.basic_blocks[-1]].live_in) == 3
@test length(lives_1.basic_blocks[lives_1.cfg.basic_blocks[-1]].live_out) == 7
@test length(lives_1.basic_blocks[lives_1.cfg.basic_blocks[-1]].def) == 7
@test length(lives_1.basic_blocks[lives_1.cfg.basic_blocks[-1]].use) == 3

deps = CompilerTools.TransitiveDependence.computeDependencies(lives_1)

#for entry in deps
#    vd = CompilerTools.LambdaHandling.getVarDef(entry[1], linfo)
#    println(entry[1], " ", entry[2], " ", vd.name)
#end

