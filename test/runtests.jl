using CompilerTools
using Base.Test

# write your own tests here
@test 1 == 1

function run_single_test(name)    
    exe_time = @elapsed include("$name.jl")
    println("test ", name, " runs in ", exe_time, " seconds")
end

function prop_err(e1,e2)
    !isa(e1,Exception) || rethrow(e1)
    !isa(e2,Exception) || rethrow(e2)
end

tests = ["test_loops_1", "test_loops_2", "test_liveness_1", "test_liveness_2", "test_alias_1", "test_alias_2", "test_alias_3"]

Base.Test.reduce(prop_err, pmap(run_single_test, tests))
println("All tests PASSED!" )
