using CompilerTools
using Base.Test

## Tests for CompilerTools.CFGs module.

# Should have only two basic blocks: starting block (does the return) and final block.
function test_fn_1()
end
ast1 = code_lowered(test_fn_1, ())[1]
cfg1 = CompilerTools.CFGs.from_ast(ast1) :: CompilerTools.CFGs.CFG

@test length(cfg1.basic_blocks) == 2

function test_fn_2(n::Int) 
    return n
end
ast2 = code_lowered(test_fn_2, (Int,))[1]
cfg2 = CompilerTools.CFGs.from_ast(ast2) :: CompilerTools.CFGs.CFG

@test length(cfg2.basic_blocks) == 2

# 4 blocks: starting block (checks n == 3), return n (implicit block), return 4, final block.
function test_fn_3(n::Int) 
    if (n == 3)
        return n
    else
        return 4
    end
end
ast3 = code_lowered(test_fn_3, (Int,))[1]
cfg3 = CompilerTools.CFGs.from_ast(ast3) :: CompilerTools.CFGs.CFG

@test length(cfg3.basic_blocks) == 4

# TODO: To write any fancier tests than this, I think we need to have
# something that filters out all the implicit basic blocks. -- LK

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

tests = ["test_loops_1", "test_loops_2", "test_liveness_1", "test_liveness_2", "test_alias_1"]

@test length(lives_1.basic_blocks[lives_1.cfg.basic_blocks[-4]].live_in) == 10
@test length(lives_1.basic_blocks[lives_1.cfg.basic_blocks[-4]].live_out) == 10
@test length(lives_1.basic_blocks[lives_1.cfg.basic_blocks[-4]].def) == 5
@test length(lives_1.basic_blocks[lives_1.cfg.basic_blocks[-4]].use) == 7

@test length(lives_1.cfg.basic_blocks) == 10
