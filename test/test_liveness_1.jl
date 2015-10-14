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
