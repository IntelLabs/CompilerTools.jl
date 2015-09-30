using CompilerTools
using Base.Test

# write your own tests here
@test 1 == 1

function runtests(name)
    @printf("     \033[1m*\033[0m \033[31m%-21s\033[0m", name)
    tt = @elapsed include("$name.jl")
    @printf(" in %6.2f seconds\n", tt)
    nothing
end

function propagate_errors(a,b)
    if isa(a,Exception)
        rethrow(a)
    end
    if isa(b,Exception)
        rethrow(b)
    end
    nothing
end

tests = ["test_loops_1", "test_loops_2", "test_liveness_1", "test_liveness_2"]

cd(dirname(@__FILE__)) do

    Base.Test.reduce(propagate_errors, nothing, pmap(runtests, tests; err_retry=false, err_stop=true))
    println("    \033[32;1mSUCCESS\033[0m" )
end