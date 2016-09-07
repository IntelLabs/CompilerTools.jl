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

module ReadWriteSet

using CompilerTools
using CompilerTools.LambdaHandling
using CompilerTools.Helper

import ..DebugMsg
DebugMsg.init()

import Base.show

#LHSVar = Union{Symbol, GenSym}

"""
Holds which scalars and which array are accessed and for array which index expressions are used.
"""
type AccessSet
    scalars :: Set{LHSVar}
    arrays  :: Dict{LHSVar, Array{Array{Any,1},1}}
    AccessSet() = new(Set{LHSVar}(), Dict{LHSVar, Array{Array{Any,1},1}}())
end

"""
Stores which scalars and arrays are read or written in some code region.
"""
type ReadWriteSetType
    readSet  :: AccessSet
    writeSet :: AccessSet
    ReadWriteSetType() = new(AccessSet(),AccessSet())
end

function getArraysAccessed(rws :: ReadWriteSetType)
    return union(collect(keys(rws.readSet.arrays)), collect(keys(rws.writeSet.arrays)))
end

export from_exprs, ReadWriteSetType, AccessSet, set_debug_level, isRead, isWritten

function merge!(outer :: AccessSet, inner :: AccessSet)
    union!(outer.scalars, inner.scalars)
    for i in inner.arrays
        key   = i[1]
        value = i[2]
        if haskey(outer.arrays, key)
            append!(outer.arrays[key], value)
        else
            outer.arrays[key] = value
        end
    end
end

function merge!(outer :: ReadWriteSetType, inner :: ReadWriteSetType)
    merge!(outer.readSet,  inner.readSet)
    merge!(outer.writeSet, inner.writeSet)
end

"""
Return true if some symbol in "sym" is read either as a scalar or array within the computed ReadWriteSetType.
"""
function isRead(sym :: LHSVar, rws :: ReadWriteSetType)
    if in(sym, rws.readSet.scalars)
        return true
    elseif haskey(rws.readSet.arrays, sym)
        return true
    else
        return false
    end
end

"""
Return true if some symbol in "sym" is written either as a scalar or array within the computed ReadWriteSetType.
"""
function isWritten(sym :: LHSVar, rws :: ReadWriteSetType)
    if in(sym, rws.writeSet.scalars)
        return true
    elseif haskey(rws.writeSet.arrays, sym)
        return true
    else
        return false
    end
end

typealias CallbackType Union{Function, Void}

"""
Walk through a lambda expression.
We just need to recurse through the lambda body and can ignore the rest.
"""
function from_lambda(ast :: Expr, depth, rws :: ReadWriteSetType, callback :: CallbackType, cbdata :: ANY)
  # :lambda expression
  body = CompilerTools.LambdaHandling.getBody(ast)
  from_expr(body, depth, rws, callback, cbdata)
  return ast
end

"""
Walk through an array of expressions.
Just recursively call from_expr for each expression in the array.
"""
function from_exprs(ast::Array)
  from_exprs(ast, 1, ReadWriteSetType(), nothing, nothing)
end

"""
Walk through an array of expressions.
Just recursively call from_expr for each expression in the array.
Takes a callback and an opaque object so that non-standard Julia AST nodes can be processed via the callback.
"""
function from_exprs(ast :: Array, callback :: CallbackType, cbdata :: ANY)
  from_exprs(ast, 1, ReadWriteSetType(), callback, cbdata)
end

"""
Walk through one AST node.
Calls the main internal walking function after initializing an empty ReadWriteSetType.
"""
function from_expr(ast :: ANY)
  from_expr(ast, 1, ReadWriteSetType(), nothing, nothing)
end

"""
Walk through one AST node.
Calls the main internal walking function after initializing an empty ReadWriteSetType.
Takes a callback and an opaque object so that non-standard Julia AST nodes can be processed via the callback.
"""
function from_expr(ast :: ANY, callback :: CallbackType, cbdata :: ANY)
  from_expr(ast, 1, ReadWriteSetType(), callback, cbdata)
end

"""
Walk through an array of expressions.
Just recursively call from_expr for each expression in the array.
Takes a callback and an opaque object so that non-standard Julia AST nodes can be processed via the callback.
Takes a ReadWriteSetType in "rws" into which information will be stored.
"""
function from_exprs(ast :: Array, depth :: Integer, rws :: ReadWriteSetType, callback :: Union{Function,Void}, cbdata :: ANY)
  # sequence of expressions
  # ast = [ expr, ... ]
  local len  = length(ast)
  @dprintln(3, "RWS starting with ", ast)
  for i = 1:len
    @dprintln(2,"RWS Processing ast #",i," depth=", depth, " ", ast[i])
    from_expr(ast[i], depth, rws, callback, cbdata)
  end
  rws
end

"""
Walk through a tuple.
Just recursively call from_exprs on the internal tuple array to process each part of the tuple.
"""
function from_tuple(ast :: Array, depth :: Integer, rws :: ReadWriteSetType, callback :: CallbackType, cbdata :: ANY)
  from_exprs(ast, depth+1, rws, callback, cbdata)
end

"""
Process a :(::) AST node.
Just process the symbol part of the :(::) node in ast[1] (which is args of the node passed in).
"""
function from_coloncolon(ast :: Array, depth :: Integer, rws :: ReadWriteSetType, callback :: CallbackType, cbdata :: ANY)
  assert(length(ast) == 2)
  from_expr(ast[1], depth+1, rws, callback, cbdata)
end

"""
Process an assignment AST node.
The left-hand side of the assignment is added to the writeSet.
"""
function from_assignment(ast :: Array{Any,1}, depth :: Integer, rws :: ReadWriteSetType, callback :: CallbackType, cbdata :: ANY)
  assert(length(ast) == 2)
  local lhs = ast[1]
  local rhs = ast[2]
  # lhs_type = typeof(lhs)
  push!(rws.writeSet.scalars, toLHSVar(lhs))
  from_expr(rhs, depth, rws, callback, cbdata)
end

"""
Takes a dictionary of symbol to an array of index expression.
Takes an array in "array_name" being accessed with expression "index_expr".
Makes sure there is an entry in the dictionary for this array and adds the index expression to this array.
"""
function addIndexExpr!(this_dict, array_name, index_expr)
  @dprintln(2,"addIndexExpr! ", typeof(array_name), " index_expr = ", index_expr, " typeof(index_expr) = ", typeof(index_expr))
  key = toLHSVar(array_name)
  if(!haskey(this_dict, key))
    this_dict[key] = Array{Any,1}[]
  end
  push!(this_dict[key], index_expr)
end

"""
Process :call Expr nodes to find arrayref and arrayset calls and adding the corresponding index expressions to the read and write sets respectively.
"""
function from_call(ast :: Expr, depth :: Integer, rws :: ReadWriteSetType, callback :: CallbackType, cbdata :: ANY)
  local fun  = getCallFunction(ast)
  local args = getCallArguments(ast)
  @dprintln(2,fun)
  for i = 1:length(args)
    @dprintln(2,"RWS from_call first arg[",i,"] = ",args[i], " type = ", typeof(args[i]))
  end
  if(isBaseFunc(fun, :arrayref) || isBaseFunc(fun, :unsafe_arrayref))
    @dprintln(2,"Handling arrayref in from_call")
    # args[1]  = array
    # args[2+] = index expressions
    assert(length(args) >= 2)
    indices = args[2:end]
    @dprintln(3, "indices = ", indices, " typeof(indices) = ", typeof(indices))
    addIndexExpr!(rws.readSet.arrays, args[1], indices)
    for j = 1:length(indices)
      from_expr(indices[j], depth, rws, callback, cbdata)
    end
  elseif (isBaseFunc(fun, :arrayset) || isBaseFunc(fun, :unsafe_arrayset))
    @dprintln(2,"Handling arrayset in from_call, length(args) = ",length(args))
    # args[1]  = array
    # args[2]  = value
    # args[3+] = index expression
    assert(length(args) >= 3)
    indices = args[3:end]
    @dprintln(3, "indices = ", indices, " typeof(indices) = ", typeof(indices))
    addIndexExpr!(rws.writeSet.arrays, args[1], indices)
    from_expr(args[2], depth, rws, callback, cbdata)
    for j = 1:length(indices)
      from_expr(indices[j], depth, rws, callback, cbdata)
    end
  elseif isBaseFunc(fun, :setfield!)
    @dprintln(2,"Handling setfield! in from_call")
    obj = toLHSVar(args[1])
    if isa(obj,LHSVar)
      push!(rws.writeSet.scalars, obj)
    end
    from_exprs(args[2:end], depth+1, rws, callback, cbdata)
  else
    @dprintln(2,"Unhandled function ", fun, " in from_call")
    from_exprs(args, depth+1, rws, callback, cbdata)
  end
end

"""
If an AST node is not recognized then we try the passing the node to the callback to see if 
it was able to process it.  If so, then we process the regular Julia statement returned by
the callback.
"""
function tryCallback(ast :: ANY, callback :: CallbackType, cbdata :: ANY, depth :: Integer, rws :: ReadWriteSetType)
  if callback != nothing
    res = callback(ast, cbdata)
  else
    res = nothing
  end
  if res != nothing
    from_exprs(res, depth+1, rws, callback, cbdata)
    return false
  end
  return true
end

function from_expr(ast :: LambdaInfo, depth :: Integer, rws :: ReadWriteSetType, callback :: CallbackType, cbdata :: ANY)
    ast = CompilerTools.LambdaHandling.getBody(ast)
    from_expr(ast, depth, rws, callback, cbdata)
    return rws
end

function from_expr(ast :: Expr, depth :: Integer, rws :: ReadWriteSetType, callback :: CallbackType, cbdata :: ANY)
    @dprintln(2,"RWS from_expr depth=", depth," ")

    @dprint(2,"RWS Expr ")
    local head = ast.head
    local args = ast.args
    local typ  = ast.typ
    @dprintln(2,head, " ", args)
    if head == :lambda
        from_lambda(ast, depth, rws, callback, cbdata)
    elseif head == :body
        from_exprs(args, depth+1, rws, callback, cbdata)
    elseif head == :block || head == :(.)
        from_exprs(args, depth+1, rws, callback, cbdata)
    elseif head == :(=)
        from_assignment(args, depth, rws, callback, cbdata)
    elseif head == :return
        from_exprs(args, depth, rws, callback, cbdata)
    elseif head == :invoke || head == :call || head == :call1
        from_call(ast, depth, rws, callback, cbdata)
        # TODO?: tuple
    elseif head == Symbol("'")
        from_exprs(args, depth, rws, callback, cbdata)
    elseif head == :line
        # skip
    elseif head == :copy
        @dprintln(3,"RWS copyast type")
        # skip
    elseif head == :copyast
        @dprintln(3,"RWS copyast type")
        # skip
    elseif head == :arraysize
        @dprintln(3,"RWS arraysize")
        # skip
    elseif head == :assertEqShape
        @dprintln(3,"RWS assertEqShape")
        # skip
    elseif head == :alloc
        from_expr(args[2], depth, rws, callback, cbdata)
    elseif head == :tuple
        @dprintln(2,"RWS tuple")
        from_tuple(args, depth, rws, callback, cbdata)
        # skip
    elseif head == :(::)
        @dprintln(2,"RWS ::")
        from_coloncolon(args, depth, rws, callback, cbdata)
    elseif head == :getindex || head == :new || head == :type_goto || head == :ccall 
        from_exprs(args, depth+1, rws, callback, cbdata)
    elseif head == :gotoifnot
        from_expr(args[1], depth, rws, callback, cbdata)
    elseif head == :meta || head == :inbounds || head == :static_parameter || 
           head == :enter || head == :leave || head == :curly || head == :the_exception ||
           head == :& || head == :static_typeof || head == :(->) || head == :(&&) ||
           head == :(||) || head == :break || head == :continue || head == Symbol("'") ||
           head == :(...) || head == :parameters || head == :kw || head == :macrocall ||
           head == :simdloop || head == :quote || head == :local || head == :let || 
           head == :while || head == :comparison || head == :if || 
           head in Set([:(+=), :(/=), :(*=), :(-=)]) || head == :for || head == :const
        # skip
    else
        #println("from_expr: unknown Expr head :", head)
        if tryCallback(ast, callback, cbdata, depth, rws)
            throw(string("from_expr: unknown Expr head :", head))
        end
    end

    return rws
end

function from_expr(ast::Union{LabelNode,GotoNode,LineNumberNode,DataType,Module,NewvarNode},
                   depth :: Integer,
                   rws :: ReadWriteSetType,
                   callback :: CallbackType,
                   cbdata::ANY)
    return rws
end

function from_expr(ast::RHSVar,
                   depth :: Integer,
                   rws :: ReadWriteSetType,
                   callback :: CallbackType,
                   cbdata::ANY)
    push!(rws.readSet.scalars, toLHSVar(ast))
    @dprintln(3,"RWS ", typeof(ast), " type")

    return rws
end

function from_expr(ast::Union{TopNode,AbstractString},
                   depth :: Integer,
                   rws :: ReadWriteSetType,
                   callback :: CallbackType,
                   cbdata::ANY)
    # skip
    @dprintln(3,"RWS ", typeof(ast), " type")

    return rws
end

function from_expr(ast::GlobalRef,
                   depth :: Integer,
                   rws :: ReadWriteSetType,
                   callback :: CallbackType,
                   cbdata::ANY)
    local mod  = ast.mod
    local name = ast.name
    @dprintln(3,"RWS GlobalRef type ",typeof(mod))
    # warn(string("from_expr: GetfieldNode typeof(mod)=", typeof(mod)))

    return rws
end

function from_expr(ast::QuoteNode,
                   depth :: Integer,
                   rws :: ReadWriteSetType,
                   callback :: CallbackType,
                   cbdata::ANY)
    local value = ast.value
    # TODO: fields: value
    @dprintln(3,"RWS QuoteNode type ",typeof(value))
    # warn(string("from_expr: QuoteNode typeof(value)=", typeof(value)))

    return rws
end

function from_expr(ast::Any,
                   depth :: Integer,
                   rws :: ReadWriteSetType,
                   callback :: CallbackType,
                   cbdata::ANY)
    asttyp = typeof(ast)

    # For Julia 0.5, Symbol won't be in RHSVar and so will come here.
    # All such uses can currently be ignored.
    if isbits(asttyp) || asttyp == Symbol
        #skip
    else
        if tryCallback(ast, callback, cbdata, depth, rws)
            throw(string("from_expr: unknown ast :", asttyp))
        end
        #@dprintln(2,"RWS from_expr: unknown AST (", typeof(ast), ",", ast, ")")
        #warn(string("from_expr: unknown AST (", typeof(ast), ",", ast, ")"))
    end
    return rws
end

function from_expr(ast::ReadWriteSetType,
                   depth :: Integer,
                   rws :: ReadWriteSetType,
                   callback :: CallbackType,
                   cbdata::ANY)
    merge!(rws, ast)
    return rws
end

end

