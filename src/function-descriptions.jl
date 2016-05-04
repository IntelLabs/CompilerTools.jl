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

# This file contains a description for a function, including the function's
# input/output arguments. 
# This gives compiler accurate information about the function without analyzing
# it. User can easily describe his/her own functions by adding entries to the
# vector below.

# A function is assumed to have the following form
#      f(argument1, argument2, ...)
# In the description, its return result is represented by number 0, 
# and its arguments by number 1, 2, and so on.
# Some arguments may be output as well, which will be described by
# the "output" field.
# ASSUMPTION: all the described is "must" information. That is, the information
# is true in all cases.
# ISSUE: depending on the specific inputs, a function "may" have different
# behavior. For example, it may update some arguments, or not update them.
# How to represent and use some "may" information?

immutable FunctionDescription
    module_name     :: AbstractString # Module of the function. It is "nothing" if it is not in a Julia module, e.g. if this is a C function 
    function_name   :: AbstractString # Name of the function
    argument_types  :: Tuple          # Tuple of the function arguments' types
    output          :: Set            # The arguments updated by the function
end

const UPDATED_NONE  = Set()
const VECTOR_OR_NUM = Tuple{Vector{}, Number}
const MATRIX_OR_NUM = Tuple{AbstractMatrix{}, Number}

const element_wise_divide1_Desc = FunctionDescription(
    "Main", 
    "./",           
    (VECTOR_OR_NUM, Vector{}),        # The arguments must be vectors
    UPDATED_NONE,                     # No argument is updated
)

const star_Desc = FunctionDescription(
    "Main", 
    "*",                              # *(A::SparseMatrixCSC, x::Vector)
    (SparseMatrixCSC, Vector{}),
    UPDATED_NONE,                     # No argument is updated
)

const star1_Desc = FunctionDescription(
    "Main", 
    "*",                              
    (Number, SparseMatrixCSC, Vector{}),
    UPDATED_NONE,                     # No argument is updated
)

const star2_Desc = FunctionDescription(
    "Main", 
    "*",           
    (Number, Vector{}),
    UPDATED_NONE,                     # No argument is updated
)

const dot_Desc = FunctionDescription(
    "Main", 
    "dot",                            # Dot(x::Vector, y::Vector)
    (Vector{}, Vector{}),             # The arguments must be vectors
    UPDATED_NONE,                     # No argument is updated
)

const copy_Desc = FunctionDescription(
    "Main", 
    "copy",
    (Vector{}, ),                     # The arguments must be a vector
    UPDATED_NONE,                     # No argument is updated
)

const add_vector_Desc = FunctionDescription(
    "Main", 
    "+",                              
    (VECTOR_OR_NUM, VECTOR_OR_NUM),
    UPDATED_NONE,                     # No argument is updated
)

const add_matrix_Desc = FunctionDescription(
    "Main", 
    "+",                              
    (MATRIX_OR_NUM, MATRIX_OR_NUM),
    UPDATED_NONE,                     # No argument is updated
)

const sub_vector_Desc = FunctionDescription(
    "Main", 
    "-",                              
    (VECTOR_OR_NUM, VECTOR_OR_NUM),
    UPDATED_NONE,                     # No argument is updated
)

const norm_Desc = FunctionDescription(
    "Main", 
    "norm",                              
    (AbstractArray, ),
    UPDATED_NONE,                     # No argument is updated
)

const spones_Desc = FunctionDescription(
    "Main", 
    "spones",                              
    (AbstractSparseMatrix{}, ),
    UPDATED_NONE,                     # No argument is updated
)

const size_Desc = FunctionDescription(
    "Main", 
    "size",                              
    (AbstractArray, Number),
    UPDATED_NONE,                     # No argument is updated
)

const Array_Desc = FunctionDescription(
    "Main", 
    "Array",                          # Array(Any, Integer)
    (Any, Integer),
    UPDATED_NONE,                     # No argument is updated
)

const fill!_Desc = FunctionDescription(
    "Main", 
    "fill!",                          
    (AbstractArray, Number),
    Set(1),                           # argument 1 is updated
)

const max_Desc = FunctionDescription(
    "Main", 
    "max",                          
    (Vector{}, Number),
    UPDATED_NONE,                     # No argument is updated
)

const scale_Desc = FunctionDescription(
    "Main", 
    "scale",                          
    (AbstractMatrix{}, Vector{}),
    UPDATED_NONE,                     # No argument is updated
)

const sum_Desc = FunctionDescription(
    "Main", 
    "sum",                          
    (AbstractArray, ),
    UPDATED_NONE,                     # No argument is updated
)

const convert_Desc = FunctionDescription(
    "Main", 
    "convert",                          
    (Array{Float64,1}, Vector{}),
    UPDATED_NONE,                     # No argument is updated
)

const eltype_Desc = FunctionDescription(
    "Main", 
    "eltype",                          
    (AbstractArray, ), 
    UPDATED_NONE,                     # No argument is updated
)

const inverse_divide_Desc = FunctionDescription(
    "Main", 
    "\\",                              
    (AbstractSparseMatrix{}, Vector{}),
    UPDATED_NONE,                     # No argument is updated
)

const fwdTriSolve!_Desc = FunctionDescription(
    "Base.SparseMatrix", 
    "fwdTriSolve!",                              
    (AbstractSparseMatrix{}, Vector{}),
    Set(2),                           # Argument 2 (the vector) is updated
)

const bwdTriSolve!_Desc = FunctionDescription(
    "Base.SparseMatrix", 
    "bwdTriSolve!",                              
    (AbstractSparseMatrix{}, Vector{}),
    Set(2),                           # Argument 2 (the vector) is updated
)

function_descriptions  = [
    element_wise_divide1_Desc,
    star_Desc,
    star1_Desc,
    star2_Desc,
    dot_Desc,
    copy_Desc,
    add_vector_Desc,
    add_matrix_Desc,
    sub_vector_Desc,
    norm_Desc,
    spones_Desc,
    size_Desc,
    Array_Desc,
    fill!_Desc,
    max_Desc,
    scale_Desc,
    sum_Desc,
    convert_Desc,
    eltype_Desc,
    inverse_divide_Desc,
    fwdTriSolve!_Desc,
    bwdTriSolve!_Desc
]

"""
Takes a module and a function both as Strings. Looks up the specified module as
part of the "Main" module and then looks and returns the Function object
corresponding to the "func" String in that module.
"""
function get_function_from_string(mod :: AbstractString, func :: AbstractString)
    # A module string may have submodules like "Base.SparseMatrix". We need to
    # get module object level by level
    modobj  = eval(:Main)
    modules = split(mod, '.')
    for m in modules
        msym = Symbol(m)
        modobj = eval(:($modobj.$msym))
    end
    
    fsym   = Symbol(func)
    return eval(:($modobj.$fsym))
end

"""
Convert the function_descriptions table into a dictionary that can be passed to
LivenessAnalysis to indicate which args are unmodified by which functions.
"""
function create_unmodified_args_dict()
    res = Dict{Tuple{Any,Array{DataType,1}}, Array{Int64,1}}()

    for desc in function_descriptions
        num_args    = length(desc.argument_types)   # Get the number of arguments to the functions.
        arg_type_array = collect(desc.argument_types)
        #println(desc.function_name, " arg_type_array = ", arg_type_array, " type = ", typeof(arg_type_array))
        unmodifieds = ones(Int64, num_args)         # desc.output contains "modifies" so we default to true and then turn off based on desc.output.
        for j in desc.output
            unmodifieds[j] = 0
        end
        res[(get_function_from_string(desc.module_name, desc.function_name), 
             arg_type_array)] = unmodifieds
    end

    return res
end
