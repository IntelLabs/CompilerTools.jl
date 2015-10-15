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

# A basic alias analysis with limited scope:
#
# 1. Only objects pointed to by variables, but not elements of arrays or other structs
# 2. We only consider variables that are assigned once
# 3. Very limited inter-precedural (i.e. function call) analysis
#
# The only useful result from this alias analysis is whether a variable definitely 
# doesn't alias with anything else, or its aliases are no longer alive. 
#
# We are NOT interested in the set of potentially aliased variables.
#
# The algorithm is basically an abstract interpreter of Julia AST.

module AliasAnalysis

import ..DebugMsg
DebugMsg.init()

using Base.uncompressed_ast
using CompilerTools.LambdaHandling
using CompilerTools

# state to keep track of variable values
const Unknown  = -1
const NotArray = 0

type State
  linfo  :: LambdaInfo
  baseID :: Int
  locals :: Dict{SymGen, Int}
  revmap :: Dict{Int, Set{SymGen}}
  nest_level :: Int
  top_level_idx :: Int
  liveness :: CompilerTools.LivenessAnalysis.BlockLiveness
end

init_state(linfo, liveness) = State(linfo, 0, Dict{SymGen,Int}(), Dict{Int, Set{SymGen}}(), 0, 0, liveness)

function increaseNestLevel(state)
state.nest_level = state.nest_level + 1
end

function decreaseNestLevel(state)
state.nest_level = state.nest_level -1
end

function next_node(state)
  local n = state.baseID + 1
  state.baseID = n
  return n
end

function update_node(state, v, w)
  if !haskey(state.locals, v)
    # new initialization
    state.locals[v] = w
    if haskey(state.revmap, w)
      push!(state.revmap[w], v)
    else
      state.revmap[w] = push!(Set{SymGen}(), v)
    end
  else
    # when a variable is initialized more than once, set to Unknown
    state.locals[v] = Unknown
    if haskey(state.revmap, w)
      for u in state.revmap[w]
        state.locals[u] = Unknown
      end
      pop!(state.revmap, w)
    end
  end
end

function update_unknown(state, v)
  state.locals[v] = Unknown
end

function update_notarray(state, v)
  state.locals[v] = NotArray
end

function update(state, v, w)
  if w > 0
    update_node(state, v, w)
  elseif w == NotArray
    update_notarray(state, v)
  else
    update_unknown(state, v)
  end
end

function toSymGen(x)
  if isa(x, SymbolNode)
    x.name
  elseif isa(x, GenSym) || isa(x, Symbol) 
    x
  else
    error("Expecting Symbol, SymbolNode, or GenSym, but got ", x)
  end
end

function lookup(state, v)
  if haskey(state.locals, v)
    state.locals[v]
  else
    Unknown
  end
end

# (:lambda, {param, meta@{localvars, types, freevars}, body})
function from_lambda(state, expr :: Expr)
  local head = expr.head
  local ast  = expr.args
  local typ  = expr.typ
  assert(length(ast) == 3)
  local linfo = lambdaExprToLambdaInfo(expr)
  # very conservative handling by setting free variables to Unknown.
  # TODO: may want to simulate function call at call site to get
  #       more accurate information.
  for (v, vd) in linfo.escaping_defs
    update_unknown(state, v)
  end
  return NotArray
end

function from_exprs(state, ast, callback=not_handled, cbdata :: ANY = nothing)
  local len  = length(ast)
  [ from_expr(state, exp, callback, cbdata) for exp in ast ]
end

function from_body(state, expr :: Expr, callback, cbdata :: ANY)
  local exprs = expr.args
  local ret = NotArray       # default return
  for i = 1:length(exprs)
    if state.nest_level == 0
      state.top_level_idx = i
    end
    ret = from_expr(state, exprs[i], callback, cbdata)
  end
  return ret
end

function from_assignment(state, expr :: Expr, callback, cbdata :: ANY)
  local head = expr.head
  local ast  = expr.args
  local typ  = expr.typ
  assert(length(ast) == 2)
  local lhs = ast[1]
  local rhs = ast[2]
  dprintln(2, "AA ", lhs, " = ", rhs)
  lhs = toSymGen(lhs)
  assert(isa(lhs, Symbol) || isa(lhs, GenSym))
  if lookup(state, lhs) != NotArray
    rhs = from_expr(state, rhs, callback, cbdata)
    # if all vars that have rhs are not alive afterwards
    # then we can safely give v a fresh ID.
    if state.nest_level == 0
      tls = CompilerTools.LivenessAnalysis.find_top_number(state.top_level_idx, state.liveness)
      assert(tls != nothing)
      assert(CompilerTools.LivenessAnalysis.isDef(lhs, tls))
      if (haskey(state.revmap, rhs))
        dead = true
        for v in state.revmap[rhs]
          dead = dead && !in(v, tls.live_out)
        end
        if dead
          rhs = next_node(state)
        end
      end
    end
    dprintln(2, "AA update ", lhs, " <- ", rhs)
    update(state, lhs, rhs)
  end
end

function from_call(state, expr :: Expr)
  # The assumption here is that the program has already been translated
  # by DomainIR, and all args are either SymbolNode or Constant.
  local head = expr.head
  local ast = expr.args
  local typ = expr.typ
  assert(length(ast) >= 1)
  local fun  = ast[1]
  local args = ast[2:end]
  dprintln(2, "AA from_call: fun=", fun, " typeof(fun)=", typeof(fun), " args=",args, " typ=", typ)
  #fun = from_expr(state, fun)
  #dprintln(2, "AA from_call: new fun=", fun)
  fun = isa(fun, TopNode) ? fun.name : fun
  fun = isa(fun, GlobalRef) ? fun.name : fun
  if is(fun, :arrayref) || is(fun, :arrayset) || is(fun, :getindex) || is(fun, :setindex!)
    # This is actually a conservative answer since arrayref might return
    # an array too, but we don't consider it as a case to handle.
    return Unknown
  elseif fun == :ccall && (args[1] == QuoteNode(:jl_new_array) || args[1] == QuoteNode(:jl_alloc_array_1d) || 
         args[1] == QuoteNode(:jl_alloc_array_2d) || args[1] == QuoteNode(:jl_alloc_array_3d))
    return next_node(state)
  elseif isa(ast[1], GlobalRef) && isFromBase(ast[1]) && endswith(string(fun), '!')
    # if the function is from base, and follow julia convention of ending with !, and
    # only one input is an array, then we consider it aliases the output
    alias = nothing
    for exp in args
      if (isa(exp, Expr) && (exp.typ == nothing || !iselementarytype(exp.typ)))
        # non-flattened input AST is not handled
        alias = Unknown
      elseif isa(exp, SymNodeGen) 
        # A local var
        typ = getType(exp, state.linfo)
        if !iselementarytype(typ)
          # complicated type
          if isarray(typ)
            # an array type!
            if !is(alias, nothing) # more than one array as input
              alias = Unknown
            else
              # remember possible match
              alias = lookup(state, toSymGen(exp))
            end
          else  
            # non array, non elementary type
            alias = Unknown
          end
        end
      end
    end
    alias = is(alias, nothing) ? Unknown : alias
    if alias == Unknown
      # if we don't know the result, it could alias any input
      for exp in args
        if isa(exp, SymbolNode)
          update_unknown(state, exp.name)
        elseif isa(exp, Symbol)
          update_unknown(state, exp)
        end
      end
    end
    return alias
  else
    dprintln(2, "AA: unknown call ", fun)
    # For unknown calls, conservative assumption is that the result
    # might alias one of (or an element of) the non-leaf-type inputs.
    for exp in args
      if isa(exp, SymbolNode)
        update_unknown(state, exp.name)
      elseif isa(exp, Symbol)
        update_unknown(state, exp)
      end
    end
    return Unknown
  end
end

function from_return(state, expr :: Expr, callback, cbdata :: ANY)
  local head = expr.head
  local typ  = expr.typ
  local args = from_exprs(state, expr.args, callback, cbdata)
  if length(args) == 1
    return args[1]
  else
    return Unknown
  end
end

function from_expr(state, ast :: ANY, callback=not_handled, cbdata :: ANY = nothing)
  if isa(ast, LambdaStaticData)
    ast = uncompressed_ast(ast)
  end

  # "nothing" output means couldn't be handled
  handled = callback(ast, state, cbdata)
  if isa(handled, Array)
    dprintln(3,"Processing expression from callback for ", ast) 
    dprintln(3,handled)
    return from_exprs(state, handled, callback, cbdata)
    # AST node replaced
  elseif isa(handled, Expr)
    ast = handled
  elseif isa(handled,Integer)
    return handled
  end


  local asttyp = typeof(ast)
  dprint(2, "AA from_expr: ", asttyp)
  if is(asttyp, Expr)
    local head = ast.head
    local args = ast.args
    local typ  = ast.typ
    dprintln(2, " --> ", head)
    if is(head, :lambda)
        return from_lambda(state, ast)
    elseif is(head, :body)
        return from_body(state, ast, callback, cbdata)
    elseif is(head, :(=))
        return from_assignment(state, ast, callback, cbdata)
    elseif is(head, :return)
        return from_return(state, ast, callback, cbdata)
    elseif is(head, :call)
        return from_call(state, ast)
        # TODO: catch domain IR result here
    elseif is(head, :call1)
      return from_call(state, ast)
    elseif is(head, :method)
        # skip
    elseif is(head, :line)
        # skip
    elseif is(head, :new)
        # skip
    elseif is(head, :boundscheck)
        # skip?
    elseif is(head, :type_goto)
        # skip?
    elseif is(head, :gotoifnot)
        # skip
    elseif is(head, :loophead)
        # skip
    elseif is(head, :loopend)
        # skip
    elseif is(head, :meta)
        # skip
    else
        throw(string("from_expr: unknown Expr head :", head))
    end
  elseif isa(ast, SymNodeGen)
    dprintln(2, " ", ast)
    return lookup(state, toSymGen(ast))
  else
    dprintln(2, " not handled ", ast)
  end
  return Unknown
end

function isFromBase(x::GlobalRef)
  startswith(string(Base.resolve(x, force=true).mod), "Base")
end

function iselementarytype(typ)
  isa(typ, DataType) && (typ.name == Type.name || eltype(typ) == typ)
end

function isarray(typ)
  isa(typ, DataType) && is(typ.name, Array.name)
end

function isbitarray(typ)
  isa(typ, DataType) && is(typ.name, BitArray.name)
end


function analyze_lambda_body(body :: Expr, lambdaInfo :: LambdaInfo, liveness, callback, cbdata :: ANY)
  local state = init_state(lambdaInfo, liveness)
  dprintln(2, "AA ", isa(body, Expr), " ", is(body.head, :body)) 
  for (v, vd) in lambdaInfo.var_defs
    if !(isarray(vd.typ) || isbitarray(vd.typ))
      update_notarray(state, v)
    end
  end
  for v in lambdaInfo.input_params
    vtyp = getType(v, lambdaInfo)
    # Note we assume all input parameters do not aliasing each other,
    # which is a very strong assumption. This may require reconsideration.
    # Update: changed to assum nothing by default.
    if isarray(vtyp) || isbitarray(vtyp)
      #update_node(state, v, next_node(state))
      update_unknown(state, v)
    end
  end
  dprintln(2, "AA locals=", state.locals)
  from_expr(state, body, callback, cbdata)
  dprintln(2, "AA locals=", state.locals)
  local revmap = Dict{Int, SymGen}()
  local unique = Set{SymGen}()
  # keep only variables that have unique object IDs.
  # TODO: should consider liveness either here or during analysis,
  #       since its ok to alias dead vars.
  for (v, w) in state.locals
    if w > 0
      if haskey(revmap, w)
        delete!(unique, revmap[w])
      else
        push!(unique, v)
        revmap[w] = v
      end
    end
  end
  dprintln(2, "AA after alias analysis: ", unique)
  # return the set of variables that are confirmed to have no aliasing
  return unique
end

function analyze_lambda(expr :: Expr, liveness, callback, cbdata :: ANY)
  lambdaInfo = lambdaExprToLambdaInfo(expr)
  analyze_lambda_body(getBody(expr), lambdaInfo, liveness, callback, cbdata)
end

end

