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

import Base.hash
import Base.isequal

export LHSVar, RHSVar, TypedVar
export TypedExpr, isArrayType, isCall, isTopNode, toLHSVar, toLHSVarOrNum, isbitstuple, isPtrType, isIntType
export isBitArrayType, isTupleType, isStringType, isequal, hasSymbol, hash, isfunctionhead

if VERSION > v"0.5.0-dev+3260"
if VERSION >= v"0.5.0-dev+3875"
typealias GenSym     SSAValue
export GenSym
end
typealias LHSVar     Union{SlotNumber, GenSym}
typealias RHSVar     Union{SlotNumber, TypedSlot, GenSym}
typealias TypedVar   TypedSlot
toLHSVar(tv::TypedVar) = SlotNumber(tv.id)
toLHSVar(tv::SlotNumber) = tv
isequal(x :: TypedVar, y :: TypedVar) = isequal(x.id, y.id) && isequal(x.typ, y.typ)
hash(x :: TypedVar) = hash(x.id)
else
typealias LHSVar     Union{Symbol, GenSym}
typealias RHSVar     Union{Symbol, SymbolNode, GenSym}
typealias TypedVar   SymbolNode
typealias LambdaInfo LambdaStaticData
toLHSVar(tv::TypedVar) = tv.name
isequal(x :: TypedVar, y :: TypedVar) = isequal(x.name, y.name) && isequal(x.typ, y.typ)
hash(x :: TypedVar) = hash(x.name)
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
isArrayType(typ::DataType) = (typ<:Array) || (typ<:BitArray)
isArrayType(x::ANY) = false
isBitArrayType(typ::DataType) = typ<:BitArray
isBitArrayType(x::ANY) = false
isPtrType(typ::DataType) = typ<:Ptr
isPtrType(typ::ANY) = false
isCall(node::Expr) = node.head==:call
isCall(node::Any) = false
isTopNode(node::TopNode) = true
isTopNode(node::Any) = false

"""
In various places we need a LHSVar type which is the union of Symbol and GenSym.
This function takes a Symbol, SymbolNode, or GenSym and return either a Symbol or GenSym.
"""
toLHSVar(x :: GenSym) = x
toLHSVar(x :: Int) = x
toLHSVar(x :: Symbol) = x
toLHSVar(x) = x
toLHSVarOrNum(x :: RHSVar) = toLHSVar(x)
toLHSVarOrNum(x :: Number) = x

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

isbitstuple(a::Any) = false
isIntType(typ::DataType) = typ<:Integer
isIntType(typ::ANY) = false
isTupleType(typ::DataType) = typ <: Tuple
isTupleType(typ::ANY) = false
isStringType(typ::DataType) = typ <: AbstractString
isStringType(typ::ANY) = false
hasSymbol(ssn :: Symbol) = true
hasSymbol(ssn :: TypedVar) = true
hasSymbol(ssn :: Expr) = ssn.head == :(::)
hasSymbol(ssn) = false

if VERSION > v"0.5.0-dev+3260"
isfunctionhead(x) = isa(x, LambdaInfo)
else
isfunctionhead(x) = isa(x, Expr) && x.head == :lambda && isa(x.args[3], Expr) && x.args[3].head == :body
end

end # module Helper


