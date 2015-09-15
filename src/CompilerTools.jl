VERSION >= v"0.4.0-dev" && __precompile__()

module CompilerTools

# package code goes here
include("ast_walk.jl")
include("lambda.jl")
include("read-write-set.jl")
include("CFGs.jl")
include("liveness.jl")
include("OptFramework.jl")
include("udchains.jl")
include("loops.jl")
include("constant_fold.jl")
include("alias-analysis.jl")

end # module
