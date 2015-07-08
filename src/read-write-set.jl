module ReadWriteSet

import Base.show

DEBUG_LVL=0

function set_debug_level(x)
    global DEBUG_LVL = x
end

function dprint(level,msgs...)
    if(DEBUG_LVL >= level)
        print(msgs...)
    end
end

function dprintln(level,msgs...)
    if(DEBUG_LVL >= level)
        println(msgs...)
    end
end

type AccessSet
    scalars :: Set
    arrays  :: Dict{Symbol,Array{Array{Any,1},1}}
    AccessSet() = new(Set(),Dict{Symbol,Array{Array{Any,1},1}}())
end

type ReadWriteSetType
    readSet  :: AccessSet
    writeSet :: AccessSet
    ReadWriteSetType() = new(AccessSet(),AccessSet())
end

export from_exprs, ReadWriteSetType, AccessSet, set_debug_level, isRead, isWritten

function isRead(sym :: Symbol, rws :: ReadWriteSetType)
    if in(sym, rws.readSet.scalars)
        return true
    elseif haskey(rws.readSet.arrays, sym)
        return true
    else
        return false
    end
end

function isWritten(sym :: Symbol, rws :: ReadWriteSetType)
    if in(sym, rws.writeSet.scalars)
        return true
    elseif haskey(rws.writeSet.arrays, sym)
        return true
    else
        return false
    end
end

uncompressed_ast(l::LambdaStaticData) =
  isa(l.ast,Expr) ? l.ast : ccall(:jl_uncompress_ast, Any, (Any,Any), l, l.ast)

# :lambda expression
# ast = [ parameters, meta (local, types, etc), body ]
function from_lambda(ast::Array{Any,1},depth, callback, cbdata)
  assert(length(ast) == 3)
  local param = ast[1]
  local meta  = ast[2]
  local body  = ast[3]
  body = from_expr(body,depth, callback, cbdata)
  ast = Array(Any, 3)
  ast[1] = param
  ast[2] = meta
  ast[3] = body
  return ast
end

function from_exprs(ast::Array)
  from_exprs(ast, 1, ReadWriteSetType(), nothing, nothing)
end

function from_exprs(ast::Array, callback, cbdata)
  from_exprs(ast, 1, ReadWriteSetType(), callback, cbdata)
end

# sequence of expressions
# ast = [ expr, ... ]
function from_exprs(ast::Array, depth, rws, callback, cbdata)
  local len  = length(ast)
  dprintln(3, "RWS starting with ", ast)
  for i = 1:len
    dprintln(2,"RWS Processing ast #",i," depth=",depth, " ", ast[i])
    from_expr(ast[i],depth,rws, callback, cbdata)
  end
  rws
end

function from_tuple(ast::Array,depth,rws, callback, cbdata)
  from_exprs(ast,depth+1,rws, callback, cbdata)
end

function from_coloncolon(ast::Array,depth,rws, callback, cbdata)
  assert(length(ast) == 2)
  from_expr(ast[1],depth+1,rws, callback, cbdata)
end

# :(=) assignment
# ast = [ ... ]
function from_assignment(ast::Array{Any,1},depth,rws, callback, cbdata)
  assert(length(ast) == 2)
  local lhs = ast[1]
  local rhs = ast[2]
  lhs_type = typeof(lhs)
  if lhs_type == Symbol
    push!(rws.writeSet.scalars,lhs)
  elseif lhs_type == SymbolNode
    push!(rws.writeSet.scalars,lhs.name)
  else
    assert(false)
  end
  from_expr(rhs,depth,rws, callback, cbdata)
end

function addIndexExpr!(this_dict, array_name, index_expr)
  dprintln(2,"addIndexExpr! ", typeof(array_name), " index_expr = ", index_expr, " typeof(index_expr) = ", typeof(index_expr))
  assert(typeof(array_name) == Symbol)
  if(!haskey(this_dict,array_name))
    this_dict[array_name] = Array{Any,1}[]
  end
  push!(this_dict[array_name],index_expr)
end

function from_call(ast::Array{Any,1}, depth, rws, callback, cbdata)
  assert(length(ast) >= 1)
  local fun  = ast[1]
  local args = ast[2:end]
  dprintln(2,fun)
  for(i = 1:length(args))
    dprintln(2,"RWS first arg[",i,"] = ",args[i], " type = ", typeof(args[i]))
  end
  if(fun == TopNode(:arrayref) || fun == TopNode(:unsafe_arrayref))
    dprintln(2,"Handling arrayref in from_call")
    # args[1]  = array
    # args[2+] = index expressions
    assert(length(args) >= 2)
    indices = args[2:end]
    dprintln(3, "indices = ", indices, " typeof(indices) = ", typeof(indices))
    addIndexExpr!(rws.readSet.arrays, args[1].name, indices)
    for j = 1:length(indices)
      from_expr(indices[j], depth, rws, callback, cbdata)
    end
  elseif (fun == TopNode(:arrayset) || fun == TopNode(:unsafe_arrayset))
    dprintln(2,"Handling arrayset in from_call, length(args) = ",length(args))
    # args[1]  = array
    # args[2]  = value
    # args[3+] = index expression
    assert(length(args) >= 3)
    indices = args[3:end]
    dprintln(3, "indices = ", indices, " typeof(indices) = ", typeof(indices))
    addIndexExpr!(rws.writeSet.arrays, args[1].name, indices)
    from_expr(args[2], depth, rws, callback, cbdata)
    for j = 1:length(indices)
      from_expr(indices[j], depth, rws, callback, cbdata)
    end
  else
    dprintln(2,"Unhandled function ", fun, " in from_call")
    from_exprs(args,depth+1, rws, callback, cbdata)
  end
end

function from_expr(ast::Any)
  from_expr(ast, 1, ReadWriteSetType(), nothing, nothing)
end

function from_expr(ast::Any, callback, cbdata)
  from_expr(ast, 1, ReadWriteSetType(), callback, cbdata)
end

function tryCallback(ast, callback, cbdata, depth, rws)
  res = callback(ast, cbdata)
  if res != nothing
    from_exprs(res,depth+1, rws, callback, cbdata)
    return false
  end
  return true
end

function from_expr(ast::Any, depth,rws, callback, cbdata)
  if typeof(ast) == LambdaStaticData
      ast = uncompressed_ast(ast)
  end
  dprintln(2,"RWS from_expr depth=",depth," ")
  local asttyp = typeof(ast)
  if asttyp == Expr
    dprint(2,"RWS Expr ")
    local head = ast.head
    local args = ast.args
    local typ  = ast.typ
    dprintln(2,head, " ", args)
    if head == :lambda
        from_lambda(args,depth,rws, callback, cbdata)
    elseif head == :body
        from_exprs(args,depth+1,rws, callback, cbdata)
    elseif head == :(=)
        from_assignment(args,depth,rws, callback, cbdata)
    elseif head == :return
        from_exprs(args,depth,rws, callback, cbdata)
    elseif head == :call
        from_call(args,depth,rws, callback, cbdata)
        # TODO: catch domain IR result here
    elseif head == :call1
        from_call(args,depth,rws, callback, cbdata)
        # TODO?: tuple
    elseif head == :line
        # skip
    elseif head == :copyast
        dprintln(3,"RWS copyast type")
        # skip
    elseif head == :arraysize
        dprintln(3,"RWS arraysize")
        # skip
    elseif head == :assertEqShape
        dprintln(3,"RWS assertEqShape")
        # skip
    elseif head == :alloc
        from_expr(args[2], depth, rws, callback, cbdata)
    elseif head == :tuple
        dprintln(2,"RWS tuple")
        from_tuple(args,depth,rws, callback, cbdata)
        # skip
    elseif head == :(::)
        dprintln(2,"RWS ::")
        from_coloncolon(args,depth,rws, callback, cbdata)
    elseif head == :new
        from_exprs(args,depth+1,rws, callback, cbdata)
    elseif head == :gotoifnot
        # skip
    else
        #println("from_expr: unknown Expr head :", head)
        if tryCallback(ast, callback, cbdata, depth, rws)
          throw(string("from_expr: unknown Expr head :", head))
        end
    end
  elseif asttyp == LabelNode
    # skip
  elseif asttyp == GotoNode
    # skip
  elseif asttyp == LineNumberNode
    # skip
  elseif asttyp == Symbol
    push!(rws.readSet.scalars,ast)
    dprintln(3,"RWS Symbol type")
    #skip
  elseif asttyp == SymbolNode # name, typ
    push!(rws.readSet.scalars,ast.name)
    dprintln(3,"RWS SymbolNode type")
    #skip
  elseif asttyp == TopNode    # name
    dprintln(3,"RWS TopNode type")
    #skip
  elseif asttyp == ASCIIString
    dprintln(3,"RWS ASCIIString type")
    #skip
  elseif asttyp == GetfieldNode
    local mod = ast.value
    local name = ast.name
    dprintln(3,"RWS GetfieldNode type ",typeof(mod))
    #warn(string("from_expr: GetfieldNode typeof(mod)=", typeof(mod)))
  elseif asttyp == DataType
    # skip
  elseif asttyp == QuoteNode
    local value = ast.value
    #TODO: fields: value
    dprintln(3,"RWS QuoteNode type ",typeof(value))
    #warn(string("from_expr: QuoteNode typeof(value)=", typeof(value)))
  elseif asttyp == Int64 || asttyp == Int32 || asttyp == Float64 || asttyp == Float32
    #skip
  else
    if tryCallback(ast, callback, cbdata, depth, rws)
      throw(string("from_expr: unknown ast :", asttyp))
    end
    #dprintln(2,"RWS from_expr: unknown AST (", typeof(ast), ",", ast, ")")
    #warn(string("from_expr: unknown AST (", typeof(ast), ",", ast, ")"))
  end
  return rws
end

end

