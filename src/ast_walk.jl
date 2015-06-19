module AstWalker

# This controls the debug print level.  0 prints nothing.  At the moment, 2 prints everything.
DEBUG_LVL=0

function set_debug_level(x)
    global DEBUG_LVL = x
end

# A debug print routine.
function dprint(level,msgs...)
    if(DEBUG_LVL >= level)
        print("AstWalk ", msgs...)
    end
end

# A debug print routine.
function dprintln(level,msgs...)
    if(DEBUG_LVL >= level)
        println("AstWalk ", msgs...)
    end
end

export AstWalk

uncompressed_ast(l::LambdaStaticData) =
  isa(l.ast,Expr) ? l.ast : ccall(:jl_uncompress_ast, Any, (Any,Any), l, l.ast)

# :lambda expression
# ast = [ parameters, meta (local, types, etc), body ]
function from_lambda(ast::Array{Any,1}, depth, callback, cbdata, top_level_number, read)
  assert(length(ast) == 3)
  param = ast[1]
  meta  = ast[2]
  body  = ast[3]

  dprintln(3,"from_lambda pre-convert param = ", param, " typeof(param) = ", typeof(param))
  for i = 1:length(param)
    param[i] = get_one(from_expr(param[i], depth, callback, cbdata, top_level_number, false, read))
  end
  dprintln(3,"from_lambda post-convert param = ", param, " typeof(param) = ", typeof(param))

  dprintln(3,"from_lambda pre-convert body = ", body, " typeof(body) = ", typeof(body))
  body = get_one(from_expr(body, depth, callback, cbdata, top_level_number, false, read))
  dprintln(3,"from_lambda post-convert body = ", body, " typeof(body) = ", typeof(body))

  ast[1] = param
  ast[2] = meta
  ast[3] = body
  return ast
end

# sequence of expressions
# ast = [ expr, ... ]
function from_exprs(ast::Array{Any,1}, depth, callback, cbdata, top_level_number, read)
  len  = length(ast)
  top_level = (top_level_number == 0)

  body = Any[]

  for i = 1:len
    if top_level
        top_level_number = length(body) + 1
        dprintln(2,"Processing top-level ast #",i," depth=",depth)
    else
        dprintln(2,"Processing ast #",i," depth=",depth)
    end

    new_exprs = from_expr(ast[i], depth, callback, cbdata, i, top_level, read)
    assert(isa(new_exprs,Array))
    append!(body, new_exprs)
  end

  return body
end

# :(=) assignment
# ast = [ ... ]
function from_assignment(ast::Array{Any,1}, depth, callback, cbdata, top_level_number, read)
#  assert(length(ast) == 2)
  ast[1] = get_one(from_expr(ast[1], depth, callback, cbdata, top_level_number, false, false))
  ast[2] = get_one(from_expr(ast[2], depth, callback, cbdata, top_level_number, false, read))
  return ast
end

function from_call(ast::Array{Any,1}, depth, callback, cbdata, top_level_number, read)
  assert(length(ast) >= 1)
  fun  = ast[1]
  args = ast[2:end]
  dprintln(2,"from_call fun = ", fun, " typeof fun = ", typeof(fun))
  if length(args) > 0
    dprintln(2,"first arg = ",args[1], " type = ", typeof(args[1]))
  end
  # symbols don't need to be translated
  if typeof(fun) != Symbol
      fun = get_one(from_expr(fun, depth, callback, cbdata, top_level_number, false, read))
  end
  args = from_exprs(args, depth+1, callback, cbdata, top_level_number, read)

  return [fun; args]
end

function AstWalk(ast::Any, callback, cbdata)
  from_expr(ast, 1, callback, cbdata, 0, false, true)
end

function get_one(ast)
  assert(isa(ast,Array))
  assert(length(ast) == 1)
  ast[1]
end

function from_expr(ast::Any, depth, callback, cbdata, top_level_number, is_top_level, read)
  if typeof(ast) == LambdaStaticData
      ast = uncompressed_ast(ast)
  end
  dprintln(2,"from_expr depth=",depth," ", " ", ast)

  ret = callback(ast, cbdata, top_level_number, is_top_level, read)
  dprintln(2,"callback ret = ",ret)
  if ret != nothing
      return [ret]
  end

  asttyp = typeof(ast)
  if asttyp == Expr
    dprint(2,"Expr ")
    head = ast.head
    args = ast.args
    typ  = ast.typ
    dprintln(2,head, " ", args)
    if head == :lambda
        args = from_lambda(args, depth, callback, cbdata, top_level_number, read)
    elseif head == :body
        args = from_exprs(args, depth+1, callback, cbdata, top_level_number, read)
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
        args[1] = get_one(from_expr(args[1], depth, callback, cbdata, top_level_number, false, read))
    elseif head == :getindex
        args = from_exprs(args,depth, callback, cbdata, top_level_number, read)
    elseif head == :new
        args = from_exprs(args,depth, callback, cbdata, top_level_number, read)
    elseif head == :arraysize
        assert(length(args) == 2)
        args[1] = get_one(from_expr(args[1], depth, callback, cbdata, top_level_number, false, read))
        args[2] = get_one(from_expr(args[2], depth, callback, cbdata, top_level_number, false, read))
    elseif head == :alloc
        assert(length(args) == 2)
        args[2] = from_exprs(args[2], depth, callback, cbdata, top_level_number, read)
    elseif head == :boundscheck
        # skip
    elseif head == :type_goto
        assert(length(args) == 2)
        args[1] = get_one(from_expr(args[1], depth, callback, cbdata, top_level_number, false, read))
        args[2] = get_one(from_expr(args[2], depth, callback, cbdata, top_level_number, false, read))
    elseif head == :tuple
        for i = 1:length(args)
          args[i] = get_one(from_expr(args[i], depth, callback, cbdata, top_level_number, false, read))
        end
    elseif head == :enter
        # skip
    elseif head == :leave
        # skip
    elseif head == :the_exception
        # skip
    elseif head == :&
        # skip
    elseif head == :ccall
        for i = 1:length(args)
          args[i] = get_one(from_expr(args[i], depth, callback, cbdata, top_level_number, false, read))
        end
    else
        throw(string("from_expr: unknown Expr head :", head, " ", ast))
    end
    ast.head = head
    ast.args = args
#    ast = Expr(head, args...)
    ast.typ = typ
  elseif asttyp == Symbol
    dprintln(2,"Symbol type")
    #skip
  elseif asttyp == SymbolNode # name, typ
    dprintln(2,"SymbolNode type")
    #skip
  elseif asttyp == TopNode    # name
    dprintln(2,"TopNode type")
    #skip
  elseif isdefined(:GetfieldNode) && asttyp == GetfieldNode  # GetfieldNode = value + name
    dprintln(2,"GetfieldNode type ",typeof(ast.value), " ", ast)
  elseif isdefined(:GlobalRef) && asttyp == GlobalRef
    dprintln(2,"GlobalRef type ",typeof(ast.mod), " ", ast)  # GlobalRef = mod + name
  elseif asttyp == QuoteNode
    value = ast.value
    #TODO: fields: value
    dprintln(2,"QuoteNode type ",typeof(value))
  elseif asttyp == LineNumberNode
    #skip
  elseif asttyp == LabelNode
    #skip
  elseif asttyp == GotoNode
    #skip
  elseif asttyp == DataType
    #skip
  elseif asttyp == ()
    #skip
  elseif asttyp == ASCIIString
    #skip
  elseif asttyp == NewvarNode
    #skip
  elseif asttyp == Nothing
    #skip
  elseif asttyp == Function
    #skip
  #elseif asttyp == Int64 || asttyp == Int32 || asttyp == Float64 || asttyp == Float32
  elseif isbits(asttyp)
    #skip
  elseif isa(ast,Tuple)
    new_tt = Expr(:tuple)
    for i = 1:length(ast)
      push!(new_tt.args, get_one(from_expr(ast[i], depth, callback, cbdata, top_level_number, false, read)))
    end
    new_tt.typ = asttyp
    ast = eval(new_tt)
  elseif asttyp == Module
    #skip
  elseif asttyp == NewvarNode
    #skip
  else
    println(ast, " type = ", typeof(ast), " asttyp = ", asttyp)
    throw(string("from_expr: unknown AST (", typeof(ast), ",", ast, ")"))
  end
  return [ast]
end

end

