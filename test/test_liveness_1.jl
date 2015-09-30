using CompilerTools
using Base.Test

## Tests for CompilerTools.LivenessAnalysis

function test_liveness_1(x::Int64, y::Int64, scale::Int64)
    Cr = (x - 256.0) / scale + 0.407476
    Ci = (y - 256.0) / scale + 0.234204
    I = 0.0
        R = 0.0
        I2 = 0.0
        R2 = 0.0
    n = 0.0
    while (R2+I2 < 2.0) && (n < 512.0)
       I = (R+R)*I+Ci;
       R = R2-I2+Cr;
       R2 = R*R;
       I2 = I*I;
       n+=1.0;
    end
    return n;
end

ast_lv_1 = code_typed(test_liveness_1, (Int64,Int64,Int64))[1]
# cfg_lv_1 = CompilerTools.CFGs.from_ast(ast_lv_1) :: CompilerTools.CFGs.CFG

#CompilerTools.LivenessAnalysis.set_debug_level(3)
function cb_func(a,b)
  nothing
end
lives_1 = CompilerTools.LivenessAnalysis.from_expr(ast_lv_1, cb_func, nothing )


@test length(lives_1.basic_blocks[lives_1.cfg.basic_blocks[-1]].live_in) == 3
@test length(lives_1.basic_blocks[lives_1.cfg.basic_blocks[-1]].live_out) == 7
@test length(lives_1.basic_blocks[lives_1.cfg.basic_blocks[-1]].def) == 7
@test length(lives_1.basic_blocks[lives_1.cfg.basic_blocks[-1]].use) == 3

@test length(lives_1.basic_blocks[lives_1.cfg.basic_blocks[-4]].live_in) == 7
@test length(lives_1.basic_blocks[lives_1.cfg.basic_blocks[-4]].live_out) == 7
@test length(lives_1.basic_blocks[lives_1.cfg.basic_blocks[-4]].def) == 5
@test length(lives_1.basic_blocks[lives_1.cfg.basic_blocks[-4]].use) == 7

@test length(lives_1.cfg.basic_blocks) == 10
