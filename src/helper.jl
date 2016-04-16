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

export SymGen, SymNodeGen, SymAllGen, SymAll
export TypedExpr, isArrayType, isCall, isTopNode, toSymGen, toSymGenOrNum, isbitstuple, isPtrType, isIntType
export isBitArrayType, isTupleType, isStringType

if VERSION > v"0.5.0-dev+3260"
typealias SymGen     Union{Symbol, Slot}
typealias SymNodeGen SymGen
typealias SymAllGen  SymGen
typealias SymAll     SymGen
else
typealias SymGen     Union{Symbol, GenSym}
typealias SymNodeGen Union{SymbolNode, GenSym}
typealias SymAllGen  Union{Symbol, SymbolNode, GenSym}
typealias SymAll     Union{Symbol, SymbolNode}
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
In various places we need a SymGen type which is the union of Symbol and GenSym.
This function takes a Symbol, SymbolNode, or GenSym and return either a Symbol or GenSym.
"""
function toSymGen(x :: Symbol)
    return x
end

if VERSION > v"0.5.0-dev+3260"
function toSymGen(x :: Slot)
    return x
end
else
function toSymGen(x :: SymbolNode)
    return x.name
end
end

function toSymGen(x :: GenSym)
    return x
end

function toSymGenOrNum(x :: SymAllGen)
    return toSymGen(x)
end

function toSymGenOrNum(x :: Number)
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
    is(typ, Int64)  || is(typ, Int32)  || is(typ, Int16)  || is(typ, Int8)  || 
    is(typ, UInt64) || is(typ, UInt32) || is(typ, UInt16) || is(typ, UInt8)
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


