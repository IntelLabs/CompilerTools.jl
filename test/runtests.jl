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

