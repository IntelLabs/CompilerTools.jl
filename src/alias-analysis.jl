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

using CompilerTools.LambdaHandling
using CompilerTools
using CompilerTools.Helper

# state to keep track of variable values
const Unknown  = -1
const NotArray = 0

type State
  linfo  :: LambdaVarInfo
  baseID :: Int
  locals :: Dict{LHSVar, Int}
  revmap :: Dict{Int, Set{LHSVar}}
  nest_level :: Int
  top_level_idx :: Int
  liveness :: CompilerTools.LivenessAnalysis.BlockLiveness
  noReAssign :: Bool
end

init_state(linfo, liveness, noReAssign) = State(linfo, 0, Dict{LHSVar,Int}(), Dict{Int, Set{LHSVar}}(), 0, 0, liveness, noReAssign)

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
      state.revmap[w] = push!(Set{LHSVar}(), v)
    end
  else
    # when a variable is initialized more than once, set to Unknown
    update_unknown(state, v)
  end
end

function update_unknown(state, v)
  old = lookup(state, v)
  state.locals[v] = Unknown
  if old > 0 && haskey(state.revmap, old)
    for u in state.revmap[old]
      state.locals[u] = Unknown
    end
    pop!(state.revmap, old)
  end
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

function lookup(state, v)
  if haskey(state.locals, v)
    state.locals[v]
  else
    Unknown
  end
end

# (:lambda, {param, meta@{localvars, types, freevars}, body})
function from_innerlambda(state, expr :: Expr)
  local head = expr.head
  local ast  = expr.args
  local typ  = expr.typ
  assert(length(ast) == 3)
  linfo, body = lambdaToLambdaVarInfo(expr)
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
  exprs = expr.args
  local ret = NotArray       # default return
  for i = 1:length(expr.args)
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
  @dprintln(2, "AA ", lhs, " = ", rhs)
  lhs = toLHSVar(lhs)
  assert(isa(lhs, LHSVar))
  if lookup(state, lhs) != NotArray
    rhs = from_expr(state, rhs, callback, cbdata)
    # if all vars that have rhs are not alive afterwards
    # then we can safely give v a fresh ID.
    @dprintln(3, "from_assignment rhs after from_expr = ", rhs)
    # Optionally allow re-assignment to be considered as non-aliasing when RHS is dead.
    if state.noReAssign == false && state.nest_level == 0
      tls = CompilerTools.LivenessAnalysis.find_top_number(state.top_level_idx, state.liveness)
      if tls == nothing
        @dprintln(0, "state.liveness = ", state.liveness)
        @dprintln(0, "state.top_level_idx = ", state.top_level_idx)
      else
        @dprintln(3, "tls = ", tls)
      end
      assert(tls != nothing)
      assert(CompilerTools.LivenessAnalysis.isDef(lhs, tls))
      if (haskey(state.revmap, rhs))
        @dprintln(3, "rhs in state.revmap")
        dead = true
        for v in state.revmap[rhs]
          @dprintln(4, "dead = ", dead, " v = ", v, " live_out = ", tls.live_out)
          dead = dead && !in(v, tls.live_out)
        end
        if dead
          @dprintln(3, "dead is true so calling next_node")
          rhs = next_node(state)
        end
      else
        @dprintln(3, "rhs not in state.revmap = ", state.revmap)
      end
    end
    @dprintln(2, "AA update ", lhs, "::", typeof(lhs), " <- ", rhs)
    update(state, lhs, rhs)
  end
end

function from_foreigncall(state, expr :: Expr, callback, cbdata)
  # The assumption here is that the program has already been translated
  # by DomainIR, and all args are either SymbolNode or Constant.
  local head = expr.head
  local ast = expr.args
  local typ = expr.typ
  assert(length(ast) >= 1)
  local fun  = ast[1]
  local args = ast[2:end]
  @dprintln(2, "AA from_foreigncall: fun=", fun, " typeof(fun)=", typeof(fun), " args=",args, " typ=", typ)

  if isa(fun, RHSVar) 
    ftyp = getType(fun, state.linfo) 
    @dprintln(2, "AA from_foreigncall: ftyp=", ftyp)
    if ftyp <: Function 
       fun = ftyp.name.name
    end
  end 

  if fun == QuoteNode(:jl_new_array) || fun == QuoteNode(:jl_alloc_array_1d) || 
     fun == QuoteNode(:jl_alloc_array_2d) || fun == QuoteNode(:jl_alloc_array_3d)
    return next_node(state)
  else
    @dprintln(2, "AA: unknown call ", fun)
    # For unknown calls, conservative assumption is that the result
    # might alias one of (or an element of) the non-leaf-type inputs.
    for exp in args
        if isa(exp, RHSVar)
            update_unknown(state, toLHSVar(exp))
        end
    end
    return Unknown
  end
end

function from_call(state, expr :: Expr, callback, cbdata)
  # The assumption here is that the program has already been translated
  # by DomainIR, and all args are either SymbolNode or Constant.
  local head = expr.head
  local ast = expr.args
  local typ = expr.typ
  assert(length(ast) >= 1)
  if head == :invoke
    # skip the first argument that is LambdaInfo
    ast = ast[2:end]
  end
  local fun  = ast[1]
  local args = ast[2:end]
  @dprintln(2, "AA from_call: fun=", fun, " typeof(fun)=", typeof(fun), " args=",args, " typ=", typ)
  #fun = from_expr(state, fun)
  #@dprintln(2, "AA from_call: new fun=", fun)
  if isa(fun, RHSVar) 
    ftyp = getType(fun, state.linfo) 
    @dprintln(2, "AA from_call: ftyp=", ftyp)
    if ftyp <: Function 
       fun = ftyp.name.name
    end
  end 
  @dprintln(2, "AA from_call: fun=", fun)
  fun = isa(fun, TopNode) ? fun.name : fun
  fun = isa(fun, GlobalRef) ? fun.name : fun
  if (fun === :reshape)
    # assume reshape's return result to always alias its first argument
    return from_expr(state, args[1], callback, cbdata)
  elseif (fun === :arrayref) || (fun === :arrayset) || (fun === :getindex) || (fun === :setindex!)
    # This is actually a conservative answer since arrayref might return
    # an array too, but we don't consider it as a case to handle.
    return Unknown
  elseif fun == :ccall && (args[1] == QuoteNode(:jl_new_array) || args[1] == QuoteNode(:jl_alloc_array_1d) || 
         args[1] == QuoteNode(:jl_alloc_array_2d) || args[1] == QuoteNode(:jl_alloc_array_3d))
    return next_node(state)
  elseif isFromBase(state, ast[1]) && endswith(string(fun), '!')
    # if the function is from base, and follow julia convention of ending with !, and
    # only one input is an array, then we consider it aliases the output
    alias = nothing
    for exp in args
      if (isa(exp, Expr) && (exp.typ == nothing || !iselementarytype(exp.typ)))
        # non-flattened input AST is not handled
        alias = Unknown
      elseif isa(exp, RHSVar) 
        # A local var
        typ = getType(exp, state.linfo)
        if !iselementarytype(typ)
          # complicated type
          if isArrayType(typ)
            # an array type!
            if !(alias === nothing) # more than one array as input
              alias = Unknown
            else
              # remember possible match
              alias = lookup(state, toLHSVar(exp))
            end
          else  
            # non array, non elementary type
            alias = Unknown
          end
        end
      end
    end
    alias = (alias === nothing) ? Unknown : alias
    if alias == Unknown
      # if we don't know the result, it could alias any input
      for exp in args
        if isa(exp, RHSVar)
            update_unknown(state, toLHSVar(exp))
        end
      end
    end
    return alias
  else
    @dprintln(2, "AA: unknown call ", fun)
    # For unknown calls, conservative assumption is that the result
    # might alias one of (or an element of) the non-leaf-type inputs.
    for exp in args
        if isa(exp, RHSVar)
            update_unknown(state, toLHSVar(exp))
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

function process_callback(handled::Array, state, ast, callback, cbdata)
    @dprintln(3,"Processing expression from callback for ", ast) 
    @dprintln(3,handled)
    return from_exprs(state, handled, callback, cbdata)
end

# AST node replaced
function process_callback(handled::Expr, state, ast, callback, cbdata)
    return from_expr_inner(state, handled, callback, cbdata)
end

function process_callback(handled::Integer, state, ast, callback, cbdata)
    return handled
end

function process_callback(handled::Any, state, ast, callback, cbdata)
    return from_expr_inner(state, ast, callback, cbdata)
end

function from_expr_inner(state, ast::Expr, callback, cbdata)
    
    local head = ast.head
    local args = ast.args
    local typ  = ast.typ
    @dprintln(2, " --> ", head)
    if (head === :lambda)
        return from_innerlambda(state, ast)
    elseif (head === :body)
        return from_body(state, ast.args, callback, cbdata)
    elseif (head === :(=))
        return from_assignment(state, ast, callback, cbdata)
    elseif (head === :return)
        return from_return(state, ast, callback, cbdata)
    elseif (head === :invoke)
        return from_call(state, ast, callback, cbdata)
    elseif (head === :call)
        return from_call(state, ast, callback, cbdata)
    elseif (head === :call1)
      return from_call(state, ast, callback, cbdata)
    elseif (head === :foreigncall)
        return from_foreigncall(state, ast, callback, cbdata)
    elseif (head === :method)
        # skip
    elseif (head === :line)
        # skip
    elseif (head === :new)
        # skip
    elseif (head === :boundscheck) || (head === :inbounds)
        # skip?
    elseif (head === :type_goto)
        # skip?
    elseif (head === :gotoifnot)
        # skip
    elseif (head === :loophead)
        # skip
    elseif (head === :loopend)
        # skip
    elseif (head === :meta)
        # skip
    elseif (head === :static_parameter)
        # skip
    elseif (head === :simdloop)
        # skip
    else
        throw(string("from_expr: unknown Expr head :", head))
    end

  return Unknown
end

function from_expr_inner(state, ast::RHSVar, callback, cbdata)
    @dprintln(2, "RHSVar ", ast, " :: ", typeof(ast))
    return lookup(state, toLHSVar(ast))
end

function from_expr_inner(state, ast::ANY, callback, cbdata)
  @dprintln(2, " not handled ", ast)
  return Unknown
end

function not_handled(a,b,c)
  nothing
end

if VERSION >= v"0.6.0-pre"
import ..LambdaHandling.LambdaInfo
end

function from_expr(state, ast::LambdaInfo, callback=not_handled, cbdata :: ANY = nothing)
    return from_expr(state, getBody(ast), callback, cbdata)
end

function from_expr(state, ast :: ANY, callback=not_handled, cbdata :: ANY = nothing)
  # "nothing" output means couldn't be handled
  handled = callback(ast, state, cbdata)
  return process_callback(handled, state, ast, callback, cbdata);
end

function isFromBase(state, x::GlobalRef)
  startswith(string(Base.resolve(x, force=true).mod), "Base")
end

function isFromBase(state, x::RHSVar)
  tname = getType(x, state.linfo).name
  isFromBase(state, GlobalRef(tname.module, tname.name))
end

function isFromBase(state, x::ANY)
  false
end

function iselementarytype(typ::DataType)
  (typ <: Type || eltype(typ) == typ)
end

function iselementarytype(typ::Any)
  return false
end

function from_lambda(LambdaVarInfo :: LambdaVarInfo, body, liveness, callback=not_handled, cbdata :: ANY = nothing; noReAssign = false)
  local state = init_state(LambdaVarInfo, liveness, noReAssign)
  #@dprintln(2, "AA ", isa(body, Expr), " ", (body.head === :body)) 
  for v in getLocalVariables(LambdaVarInfo)
    vtyp = getType(v, LambdaVarInfo)
    @dprintln(2, "v = ", v, " vtyp = ", vtyp)
    if !isArrayType(vtyp)
      update_notarray(state, v)
    elseif isInputParameter(v, LambdaVarInfo)
      update_unknown(state, v)
    end
  end
  @dprintln(2, "AA locals=", state.locals)
  from_body(state, body, callback, cbdata)
  @dprintln(2, "AA locals=", state.locals)
  local revmap = Dict{Int, LHSVar}()
  local unique = Set{LHSVar}()
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
  @dprintln(2, "AA after alias analysis: ", unique)
  # return the set of variables that are confirmed to have no aliasing
  return unique
end

function from_lambda(expr, liveness, callback=not_handled, cbdata :: ANY = nothing; noReAssign = false)
  LambdaVarInfo, body = lambdaToLambdaVarInfo(expr)
  from_lambda(LambdaVarInfo, body, liveness, callback, cbdata; noReAssign = noReAssign)
end

end

