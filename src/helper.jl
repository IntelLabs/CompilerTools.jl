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

"""
A collection of helper functions for processing AST nodes
"""
module Helper

export LHSVar, RHSVar, TypedVar
export TypedExpr, isArrayType, isCall, isTopNode, toLHSVar, toLHSVarOrNum, isbitstuple, isPtrType, isIntType
export isBitArrayType, isTupleType, isStringType



if VERSION > v"0.5.0-dev+3260"
typealias LHSVar     Union{Int, GenSym}
typealias RHSVar     Union{Slot, GenSym}
typealias TypedVar   Slot
else
typealias LHSVar     Union{Symbol, GenSym}
typealias RHSVar     Union{Symbol, SymbolNode, GenSym}
typealias TypedVar   SymbolNode
typealias LambdaInfo LambdaStaticData
export LambdaInfo
end

"""
This should always be used instead of Expr(...) to form an expression as it forces the typ to be provided.
"""
function TypedExpr(typ, rest...)
    res = Expr(rest...)
    res.typ = typ
    res
end

"""
Returns true if the incoming type in "typ" is an array type.
"""
function isArrayType(typ::DataType)
    (typ<:Array) || (typ<:BitArray)
end

function isArrayType(x::ANY)
    false
end

function isBitArrayType(typ::DataType)
    typ<:BitArray
end

function isBitArrayType(x::ANY)
    false
end

function isPtrType(typ::DataType)
    typ<:Ptr
end

function isPtrType(typ::ANY)
    return false
end


function isCall(node::Expr)
    return node.head==:call
end

function isCall(node::Any)
    return false
end

function isTopNode(node::TopNode)
    return true
end

function isTopNode(node::Any)
    return false
end

"""
In various places we need a LHSVar type which is the union of Symbol and GenSym.
This function takes a Symbol, SymbolNode, or GenSym and return either a Symbol or GenSym.
"""
function toLHSVar(x :: GenSym)
    return x
end

if VERSION > v"0.5.0-dev+3260"
function toLHSVar(x :: Slot)
    return x.id
end
function toLHSVar(x :: Int)
    return x
end
else
function toLHSVar(x :: SymbolNode)
    return x.name
end
function toLHSVar(x :: Symbol)
    return x
end
end

function toLHSVarOrNum(x :: RHSVar)
    return toLHSVar(x)
end

function toLHSVarOrNum(x :: Number)
    return x
end


"""
Returns true if input "a" is a tuple and each element of the tuple of isbits type.
"""
function isbitstuple(a::Tuple)
    for i in a
        if !isbits(i)
            return false
        end
    end
    return true
end

function isbitstuple(a::Any)
    return false
end

function isIntType(typ::DataType)
    typ<:Integer
end

function isIntType(typ::ANY)
    return false
end

function isTupleType(typ::DataType)
    typ <: Tuple
end

function isTupleType(typ::ANY)
    return false
end

function isStringType(typ::DataType)
    typ <: AbstractString
end

function isStringType(typ::ANY)
    return false
end

end # module Helper


