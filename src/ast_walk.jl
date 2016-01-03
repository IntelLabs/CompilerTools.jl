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

module AstWalker

import ..DebugMsg
DebugMsg.init()

# Return this value to indicate to AstWalk to recursively process the given node.
immutable ASTWALK_RECURSE
end

immutable ASTWALK_REMOVE
end

export AstWalk, ASTWALK_RECURSE, ASTWALK_REMOVE

"""
Convert a compressed LambdaStaticData format into the uncompressed AST format.
"""
uncompressed_ast(l::LambdaStaticData) =
  isa(l.ast,Expr) ? l.ast : ccall(:jl_uncompress_ast, Any, (Any,Any), l, l.ast)

"""
AstWalk through a lambda expression.
Walk through each input parameters and the body of the lambda.
"""
# TODO - it seems we should walk some parts of meta as well.
function from_lambda(ast :: Array{Any,1}, depth, callback, cbdata :: ANY, top_level_number, read)
  assert(length(ast) == 3)
  param = ast[1]
  meta  = ast[2]
  body  = ast[3]

  dprintln(3,"from_lambda pre-convert param = ", param, " typeof(param) = ", typeof(param))
  for i = 1:length(param)
    dprintln(3,"from_lambda param[i] = ", param[i], " typeof(param[i]) = ", typeof(param[i]))
    param[i] = from_expr(param[i], depth, callback, cbdata, top_level_number, false, read)
  end
  dprintln(3,"from_lambda post-convert param = ", param, " typeof(param) = ", typeof(param))

  dprintln(3,"from_lambda pre-convert body = ", body, " typeof(body) = ", typeof(body))
  body = from_expr(body, depth, callback, cbdata, top_level_number, false, read)
  dprintln(3,"from_lambda post-convert body = ", body, " typeof(body) = ", typeof(body))
  if typeof(body) != Expr || body.head != :body
    dprintln(0,"AstWalk from_lambda got a non-body returned from procesing body")
    dprintln(0,body)
    throw(string("big problem"))
  end

  ast[1] = param
  ast[2] = meta
  ast[3] = body
  return ast
end

"""
AstWalk through a function body.
"""
function from_body(ast :: Array{Any,1}, depth, callback, cbdata :: ANY, top_level_number, read)
  len = length(ast)
  top_level = true

  body = Any[]

  for i = 1:len
    dprintln(2,"Processing top-level ast #",i," depth=",depth)

    dprintln(3,"AstWalk from_exprs, ast[", i, "] = ", ast[i])
    new_expr = from_expr(ast[i], depth, callback, cbdata, i, top_level, read)
    dprintln(3,"AstWalk from_exprs done, ast[", i, "] = ", new_expr)
    if new_expr != ASTWALK_REMOVE
      push!(body, new_expr)
    end
  end

  return body
end

"""
AstWalk through an array of expressions.
"""
function from_exprs(ast :: Array{Any,1}, depth, callback, cbdata :: ANY, top_level_number, read)
  len = length(ast)
  top_level = false

  body = Any[]

  for i = 1:len
    dprintln(2,"Processing ast #",i," depth=",depth)
    dprintln(3,"AstWalk from_exprs, ast[", i, "] = ", ast[i])
    new_expr = from_expr(ast[i], depth, callback, cbdata, i, top_level, read)
    dprintln(3,"AstWalk from_exprs done, ast[", i, "] = ", new_expr)
    if new_expr != ASTWALK_REMOVE
      push!(body, new_expr)
    end
  end

  return body
end

"""
AstWalk through an assignment expression.
Recursively process the left and right hand sides with AstWalk.
"""
function from_assignment(ast :: Array{Any,1}, depth, callback, cbdata :: ANY, top_level_number, read)
#  assert(length(ast) == 2)
  dprintln(3,"from_assignment, lhs = ", ast[1])
  ast[1] = from_expr(ast[1], depth, callback, cbdata, top_level_number, false, false)
  dprintln(3,"from_assignment, rhs = ", ast[2])
  ast[2] = from_expr(ast[2], depth, callback, cbdata, top_level_number, false, read)
  return ast
end

"""
AstWalk through a call expression.
Recursively process the name of the function and each of its arguments.
"""
function from_call(ast :: Array{Any,1}, depth, callback, cbdata :: ANY, top_level_number, read)
  assert(length(ast) >= 1)
  fun  = ast[1]
  args = ast[2:end]
  dprintln(2,"from_call fun = ", fun, " typeof fun = ", typeof(fun))
  if length(args) > 0
    dprintln(2,"first arg = ",args[1], " type = ", typeof(args[1]))
  end
  # symbols don't need to be translated
  if typeof(fun) != Symbol
      fun = from_expr(fun, depth, callback, cbdata, top_level_number, false, read)
  end
  args = from_exprs(args, depth+1, callback, cbdata, top_level_number, read)

  return [fun; args]
end

"""
Entry point into the code to perform an AST walk.
You generally pass a lambda expression as the first argument.
The third argument is an object that is opaque to AstWalk but that is passed to every callback.
You can use this object to collect data about the AST as it is walked or to hold information on
how to change the AST as you are walking over it.
The second argument is a callback function.  For each AST node, AstWalk will invoke this callback.
The signature of the callback must be (Any, Any, Int64, Bool, Bool).  The arguments to the callback
are as follows:
    1) The current node of the AST being walked.
    2) The callback data object that you originally passed as the first argument to AstWalk.
    3) Specifies the index of the body's statement that is currently being processed.
    4) True if the current AST node being walked is the root of a top-level statement, false if the AST node is a sub-tree of a top-level statement.
    5) True if the AST node is being read, false if it is being written.
The callback should return an array of items.  It does this because in some cases it makes sense to return multiple things so
all callbacks have to to keep the interface consistent.
"""
function AstWalk(ast :: ANY, callback, cbdata :: ANY)
  from_expr(ast, 1, callback, cbdata, 0, false, true)
end

"""
The main routine that switches on all the various AST node types.
The internal nodes of the AST are of type Expr with various different Expr.head field values such as :lambda, :body, :block, etc.
The leaf nodes of the AST all have different types.
There are some node types we don't currently recurse into.  Maybe this needs to be extended.
"""
function from_expr(ast :: ANY, depth, callback, cbdata :: ANY, top_level_number, is_top_level, read)
    if typeof(ast) == LambdaStaticData
        ast = uncompressed_ast(ast)
    end
    dprintln(2,"from_expr depth=",depth," ", " ", ast)

    ret = callback(ast, cbdata, top_level_number, is_top_level, read)
    dprintln(2,"callback ret = ",ret)
    if ret != ASTWALK_RECURSE
        return ret
    end

    ast = from_expr_helper(ast, depth, callback, cbdata, top_level_number, is_top_level, read)

    dprintln(3,"Before return for ", ast)
    return ast
end

function from_expr_helper(ast::Expr,
                          depth,
                          callback,
                          cbdata::ANY,
                          top_level_number,
                          is_top_level,
                          read)
    dprint(2,"Expr ")
    head = ast.head
    args = ast.args
    typ  = ast.typ
    dprintln(2,head, " ", args)
    if head == :lambda
        args = from_lambda(args, depth, callback, cbdata, top_level_number, read)
    elseif head == :body
        dprintln(2,"Processing :body Expr in AstWalker.from_expr")
        args = from_body(args, depth+1, callback, cbdata, top_level_number, read)
        dprintln(2,"Done processing :body Expr in AstWalker.from_expr")
    elseif head == :block
        args = from_exprs(args, depth+1, callback, cbdata, top_level_number, read)
    elseif head == :(.)
        args = from_exprs(args, depth+1, callback, cbdata, top_level_number, read)
    elseif head == :(=)
        args = from_assignment(args, depth, callback, cbdata, top_level_number, read)
    elseif head == :(::)
        assert(length(args) == 2)
        dprintln(3, ":: args[1] = ", args[1])
        dprintln(3, ":: args[2] = ", args[2])
        args[1] = from_expr(args[1], depth, callback, cbdata, top_level_number, false, read)
    elseif head == :return
        args = from_exprs(args, depth, callback, cbdata, top_level_number, read)
    elseif head == :call
        args = from_call(args, depth, callback, cbdata, top_level_number, read)
        # TODO: catch domain IR result here
    elseif head == :call1
        args = from_call(args, depth, callback, cbdata, top_level_number, read)
        # TODO?: tuple
    elseif head == :line
        # skip
    elseif head == :copy
        # turn array copy back to plain Julia call
        head = :call
        args = vcat(:copy, args)
    elseif head == :copyast
        dprintln(2,"copyast type")
        # skip
    elseif head == :gotoifnot
        assert(length(args) == 2)
        args[1] = from_expr(args[1], depth, callback, cbdata, top_level_number, false, read)
    elseif head == :getindex
        args = from_exprs(args,depth, callback, cbdata, top_level_number, read)
    elseif head == :new
        args = from_exprs(args,depth, callback, cbdata, top_level_number, read)
    elseif head == :arraysize
        assert(length(args) == 2)
        args[1] = from_expr(args[1], depth, callback, cbdata, top_level_number, false, read)
        args[2] = from_expr(args[2], depth, callback, cbdata, top_level_number, false, read)
    elseif head == :alloc
        assert(length(args) == 2)
        args[2] = from_exprs(args[2], depth, callback, cbdata, top_level_number, read)
    elseif head == :boundscheck
        # skip
    elseif head == :type_goto
        assert(length(args) == 2)
        args[1] = from_expr(args[1], depth, callback, cbdata, top_level_number, false, read)
        args[2] = from_expr(args[2], depth, callback, cbdata, top_level_number, false, read)
    elseif head == :tuple
        for i = 1:length(args)
            args[i] = from_expr(args[i], depth, callback, cbdata, top_level_number, false, read)
        end
    elseif head == :enter
        # skip
    elseif head == :leave
        # skip
    elseif head == :curly
        # skip
    elseif head == :the_exception
        # skip
    elseif head == :&
        # skip
    elseif head == :static_typeof
        for i = 1:length(args)
            args[i] = from_expr(args[i], depth, callback, cbdata, top_level_number, false, read)
        end
    elseif head == :ccall
        for i = 1:length(args)
            args[i] = from_expr(args[i], depth, callback, cbdata, top_level_number, false, read)
        end
    elseif head == :function
	dprintln(3,"in function head")
	args[2] = from_expr(args[2], depth, callback, cbdata, top_level_number, false, read)
    elseif head == :vcat || head == :typed_vcat || head == :hcat || head == :typed_hcat
	dprintln(3,"in vcat head")
	#skip
    elseif head == :ref
	for i = 1:length(args)
	    args[i] = from_expr(args[i], depth, callback, cbdata, top_level_number, false, read)
	end
    elseif head == :meta
	# ignore :meta for now. TODO: we might need to walk its args.
    elseif head == :comprehension || head == :vect
	# args are either Expr or Symbol
	for i = 1:length(args)
	    args[i] = from_expr(args[i], depth, callback, cbdata, top_level_number, false, read)
	end
    elseif head == :typed_comprehension
	# args are either Expr or Symbol
	for i = 1:length(args)
	    args[i] = from_expr(args[i], depth, callback, cbdata, top_level_number, false, read)
	end
    elseif head == :(->) || head == :(&&) || head == :(||)
	# args are either Expr or Symbol
	for i = 1:length(args)
	    args[i] = from_expr(args[i], depth, callback, cbdata, top_level_number, false, read)
	end
    elseif head == :(:)
	# args are either Expr or Symbol
	for i = 1:length(args)
	    args[i] = from_expr(args[i], depth, callback, cbdata, top_level_number, false, read)
	end
    elseif head == :const
	dump(ast,1000)
	# ignore :const for now.
    elseif head == :for
	for i = 1:length(args)
	    args[i] = from_expr(args[i], depth, callback, cbdata, top_level_number, false, read)
	end
    elseif head in Set([:(+=), :(/=), :(*=), :(-=)])
        args[1] = from_expr(args[1], depth, callback, cbdata, top_level_number, false, false)
        args[2] = from_expr(args[2], depth, callback, cbdata, top_level_number, false, read)
    elseif head == :if
	for i = 1:length(args)
	    args[i] = from_expr(args[i], depth, callback, cbdata, top_level_number, false, read)
	end
    elseif head == :comparison
	for i = 1:length(args)
	    args[i] = from_expr(args[i], depth, callback, cbdata, top_level_number, false, read)
	end
    elseif head == :while
	for i = 1:length(args)
	    args[i] = from_expr(args[i], depth, callback, cbdata, top_level_number, false, read)
	end
    elseif head == :let
	for i = 1:length(args)
	    args[i] = from_expr(args[i], depth, callback, cbdata, top_level_number, false, read)
	end
    elseif head == :local
	for i = 1:length(args)
	    args[i] = from_expr(args[i], depth, callback, cbdata, top_level_number, false, read)
	end
    elseif head == :quote
	for i = 1:length(args)
	    args[i] = from_expr(args[i], depth, callback, cbdata, top_level_number, false, read)
	end
    elseif head == :simdloop
        # skip
    elseif head == :macrocall
        for i = 1:length(args)
            args[i] = from_expr(args[i], depth, callback, cbdata, top_level_number, false, read)
        end
    elseif head == :(...) || head == :parameters || head == :kw
        args[1] = from_expr(args[1], depth, callback, cbdata, top_level_number, false, read)
    elseif head == symbol("'")
        for i = 1:length(args)
            args[i] = from_expr(args[i], depth, callback, cbdata, top_level_number, false, read)
        end
    else
        throw(string("CompilerTools.AstWalker.from_expr: unknown Expr head :", head, " in ", ast))
    end
    ast.head = head
    ast.args = args
    # ast = Expr(head, args...)
    ast.typ = typ

    return ast
end

function from_expr_helper(ast::Union{Symbol,GenSym,SymbolNode,TopNode},
                          depth,
                          callback,
                          cbdata::ANY,
                          top_level_number,
                          is_top_level,
                          read)
    dprintln(2, typeof(ast), " type")
    # Intentionally do nothing.
    return ast
end

function from_expr_helper(ast::Union{LineNumberNode,LabelNode,GotoNode,DataType,ASCIIString,UTF8String,NewvarNode,Void,Function,Module},
                          depth,
                          callback,
                          cbdata::ANY,
                          top_level_number,
                          is_top_level,
                          read)
    # Intentionally do nothing.
    return ast
end

function from_expr_helper(ast::Tuple,
                          depth,
                          callback,
                          cbdata::ANY,
                          top_level_number,
                          is_top_level,
                          read)

    # N.B. This also handles the empty tuple correctly.

    new_tt = Expr(:tuple)
    for i = 1:length(ast)
        push!(new_tt.args, from_expr(ast[i], depth, callback, cbdata, top_level_number, false, read))
    end
    new_tt.typ = asttyp
    ast = eval(new_tt)

    return ast
end

function from_expr_helper(ast::QuoteNode,
                          depth,
                          callback,
                          cbdata::ANY,
                          top_level_number,
                          is_top_level,
                          read)
    value = ast.value
    #TODO: fields: value
    dprintln(2,"QuoteNode type ",typeof(value))

    return ast
end

function from_expr_helper(ast::Any,
                          depth,
                          callback,
                          cbdata::ANY,
                          top_level_number,
                          is_top_level,
                          read)
    asttyp = typeof(ast)

    if isdefined(:GetfieldNode) && asttyp == GetfieldNode  # GetfieldNode = value + name
        dprintln(2,"GetfieldNode type ",typeof(ast.value), " ", ast)
    elseif isdefined(:GlobalRef) && asttyp == GlobalRef
        dprintln(2,"GlobalRef type ",typeof(ast.mod), " ", ast)  # GlobalRef = mod + name
    elseif isbits(asttyp)
        #skip
    else
        println(ast, " type = ", typeof(ast), " asttyp = ", asttyp)
        throw(string("from_expr: unknown AST (", typeof(ast), ",", ast, ")"))
    end

    return ast
end

end
