module LambdaHandling

import Base.show

# This controls the debug print level.  0 prints nothing.  At the moment, 2 prints everything.
DEBUG_LVL=0

function set_debug_level(x)
    global DEBUG_LVL = x
end

# A debug print routine.
function dprint(level,msgs...)
    if(DEBUG_LVL >= level)
        print(msgs...)
    end
end

# A debug print routine.
function dprintln(level,msgs...)
    if(DEBUG_LVL >= level)
        println(msgs...)
    end
end

type VarDef
  name :: Symbol
  typ
  desc :: Int64

  function VarDef(n, t, d)
    new(n, t, d)
  end
end

type LambdaInfo
  input_params :: Set{Symbol}
  var_defs     :: Dict{Symbol,VarDef}
  gen_syms     :: Array{Any,1}
  captured_outer_vars :: Array{Any,1}
  static_parameter_names :: Array{Any,1}

  function LambdaInfo()
    new(Set{Symbol}(), Dict{Symbol,VarDef}(), Any[], Any[], Any[])
  end
end

function createVarSet(x :: Array{Any,1})
  ret = Set{Symbol}()
  for i = 1:length(x)
    assert(typeof(x[i]) == Symbol)
    push!(ret, x[i])
  end
  return ret
end

function createVarDict(x :: Array{Any, 1})
  ret = Dict{Symbol,VarDef}()
  dprintln(1,"createVarDict ", x)
  for i = 1:length(x)
    dprintln(1,"x[i] = ", x[i])
    name = x[i][1]
    typ  = x[i][2]
    desc = x[i][3]
    if typeof(name) != Symbol
      dprintln(0, "name is not of type symbol ", name, " type = ", typeof(name))
    end
    if typeof(desc) != Int64
      dprintln(0, "desc is not of type Int64 ", desc, " type = ", typeof(desc))
    end
    ret[name] = VarDef(name, typ, desc)
  end
  return ret
end

function lambdaExprToLambdaInfo(lambda :: Expr)
  assert(lambda.head == :lambda)

  ret = LambdaInfo()
  # Convert array of input parameters in lambda.args[1] into a searchable Set.
  ret.input_params = createVarSet(lambda.args[1]) 
  # We call the second part of the lambda metadata.
  meta = lambda.args[2]
  dprintln(1,"meta = ", meta)
  # Create a searchable dictionary mapping symbols to their VarDef information.
  ret.var_defs = createVarDict(meta[1])
  ret.captured_outer_vars = meta[2]
  ret.gen_syms = meta[3]
  ret.static_parameter_names = meta[4]

  return ret
end

function setToArray(x :: Set{Symbol})
  ret = Symbol[]
  for s in x
    push!(ret, s)
  end
  return ret
end

function dictToArray(x :: Dict{Symbol,VarDef})
  ret = Any[]
  for s in x
    push!(ret, [s.name; s.typ; s.desc])
  end
  return ret
end

function createMeta(lambdaInfo :: LambdaInfo)
  ret = Any[]

  push!(ret, dictToArray(lambdaInfo.var_defs))
  push!(ret, captured_outer_vars)
  push!(ret, gen_syms)
  push!(ret, static_parameter_names)

  return ret
end

function lambdaInfoToLambdaExpr(lambdaInfo :: LambdaInfo, body)
  return Expr(:lambda, setToArray(lambdaInfo.input_params), createMeta(lambdaInfo), body)
end

function getBody(lambda :: Expr)
  assert(lambda.head == :lambda)
  return lambda.args[3]
end

function getRefParams(lambdaInfo :: LambdaInfo)
  ret = Symbol[]

  input_vars = lambdaInfo.input_params
  var_types  = lambdaInfo.var_defs

  dprintln(3,"input_vars = ", input_vars)
  dprintln(3,"var_types = ", var_types)

  for iv in input_vars
    dprintln(3,"iv = ", iv, " type = ", typeof(iv))
    if haskey(var_types, iv)
      var_def = var_types[iv] 
      if !isbits(var_def.typ)
        push!(ret, iv)
      end
    else
      throw(string("Didn't find parameter variable ", iv, " in type list."))
    end
  end

  return ret
end

end
