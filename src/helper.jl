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

using ..LambdaHandling

export TypedExpr, isArrayType, isCall, isTopNode, toSymGen


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
    return (typ.name == Array.name || typ.name == BitArray.name)
end


"""
Returns true if a given SymbolNode "x" is an Array type.
"""
function isArrayType(x :: SymbolNode)
    the_type = x.typ
    if typeof(the_type) == DataType
        return isArrayType(x.typ)
    end
    return false
end

function isArrayType(x::ANY)
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

function toSymGen(x :: SymbolNode)
    return x.name
end

function toSymGen(x :: GenSym)
    return x
end


end # module Helper


