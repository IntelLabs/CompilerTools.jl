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

module LambdaHandling

import ..DebugMsg
DebugMsg.init()

using CompilerTools
using ..Helper
import ..Helper.toLHSVar
using CompilerTools.AstWalker
using Core.Inference: to_tuple_type

import Base.show

export VarDef, LambdaVarInfo, toRHSVar, lookupLHSVarByName, lookupVariableName
export getDesc, setDesc, getType, setType, getReturnType, setReturnType 
export isInputParameter, getInputParameters, setInputParameters, getInputParametersAsExpr
export isEscapingVariable, getEscapingVariables, addEscapingVariable, setEscapingVariable, unsetEscapingVariable
export isLocalVariable, getLocalVariables, getLocalVariablesNoParam, addLocalVariable, addTempVariable
export getBody, getReturnType, setReturnType
export lambdaToLambdaVarInfo, LambdaVarInfoToLambda, lambdaTypeinf, prependStatements
export getRefParams, getArrayParams, updateAssignedDesc, getEscapingVariablesAsLHSVar
export mergeLambdaVarInfo, replaceExprWithDict!, countVariables
export ISCAPTURED, ISASSIGNED, ISASSIGNEDBYINNERFUNCTION, ISCONST, ISASSIGNEDONCE 

# Possible values of VarDef descriptor that can be OR'ed together.
const ISCAPTURED = 1
const ISASSIGNED = 2
const ISASSIGNEDBYINNERFUNCTION = 4
const ISCONST = 8
const ISASSIGNEDONCE = 16

const digits = Char[x for x in "0123456789" ]

if VERSION >= v"0.5.0-dev+3875"
typealias DescType UInt8
else
typealias DescType Int64
end

const emptyVarName = Symbol("")

"""
Represents a variable's definition, including its (optional) symbol, type, desc, and (optional) id.
"""
type VarDef
  name :: Symbol
  typ  :: Type
  desc :: DescType
  id   :: Int

  function VarDef(n::Symbol, t::Type, d::DescType, i::Int)
    new(n, t, d, i)
  end

  # no id, assuming -1.
  function VarDef(n::Symbol, t::Type, d::DescType)
    new(n, t, d, -1)
  end

  # no symbol name, meaning GenSym (or SSAValue)
  function VarDef(t::Type, d::DescType, i::Int)
    new(emptyVarName, t, d, i)
  end
end

type LambdaVarInfo
  input_params  :: Array{Symbol,1}          # input parameters always have a name symbol 
  vararg_params :: Array{Symbol,1}          # record which parameter is vararg
  escaping_vars :: Array{Symbol,1}          # escaping variables always have a name symbol
  var_defs      :: Array{VarDef}            # all variable definitions
  static_parameter_names :: Array{Any,1}
  return_type   :: Any
  orig_info     :: Union{LambdaInfo,Void}

  function LambdaVarInfo()
    new(Symbol[], Symbol[], Symbol[], VarDef[], Any[], Void, nothing)
  end

  function LambdaVarInfo(li::LambdaVarInfo)
    new(copy(li.input_params), copy(li.vararg_params), copy(li.escaping_vars), copy(li.var_defs), 
        copy(li.static_parameter_names), li.return_type, li.orig_info == nothing ? nothing : copy(li.orig_info))
  end

if VERSION >= v"0.5.0-dev+3875"
  function LambdaVarInfo(lambda::LambdaInfo, body)
    @dprintln(3, "lambda = ", lambda)
    return_typ = lambda.rettype
    input_params = Symbol[]
    vararg_params = Symbol[]
    var_defs = VarDef[]
    escaping_vars = Symbol[]
    allnames = Set{Symbol}()
    for i = 1:length(lambda.slotnames)
        name = lambda.slotnames[i]
        typ = lambda.slottypes[i]
        desc = lambda.slotflags[i]
        if in(name, allnames)
            name = Symbol(string(name, "@", i))
        elseif startswith(string(name), digits) # numerical names are very confusing, fix them!
            name = Symbol(string("@", name))
        end
        push!(allnames, name)
        vd = VarDef(name, typ, desc, i)
        push!(var_defs, vd)
        # skip #self# in parameters
        if i > 1 && i <= lambda.nargs
            push!(input_params, name)
        end
    end

    for i = 1:length(lambda.ssavaluetypes)
        vd = VarDef(emptyVarName, lambda.ssavaluetypes[i], convert(DescType, ISASSIGNED | ISASSIGNEDONCE), i-1)
        push!(var_defs, vd)
    end
    x = new(input_params, vararg_params, Symbol[], var_defs, Any[], return_typ, lambda)
    @dprintln(3, "LambdaVarInfo = ", x)
    return x
  end
else
  function LambdaVarInfo(lambda::LambdaInfo, ast)
    li = LambdaVarInfo(ast)
    li.orig_info = lambda
    return li
  end

  function LambdaVarInfo(lambda::Expr)
    @assert (lambda.head == :lambda) "Expect a lambda Expr as argument to LambdaVarInfo(..)"
    assert(length(lambda.args) == 3) 

    input_params = Symbol[]
    vararg_params = Symbol[]
    var_defs = VarDef[]
    escaping_vars = Symbol[]

    #parameters
    for i = 1:length(lambda.args[1])
        p = lambda.args[1][i] 
        if isa(p, Symbol)
          push!(input_params, p)
        elseif isa(p, SymbolNode)
          push!(input_params, p.name)
        elseif isa(p, Expr) && (p.head == :(::))
          @dprintln(3, "Got typed parameter: ", p)
          assert(isa(p.args[1], Symbol)) 
          push!(input_params, p.args[1])
          if isa(p.args[2], Expr) && p.args[2].head == :(...)
            push!(vararg_params, p.args[1])
          end
        end
    end 

    meta = lambda.args[2]
    assert(length(meta) >= 3)
    #local variables (including parameter and its type)
    locals = meta[1]
    for i = 1:length(locals)
        name = locals[i][1]
        typ  = locals[i][2]
        desc = locals[i][3]
        @assert (isa(name, Symbol)) "Expect local variable name to be Symbol, but got " * string(name)
        @assert (isa(typ, Type)) "Expect local variable type, but got " * string(typ)
        @assert (isa(desc, DescType)) "Expect local variable desc to be " * string(DescType) * " but got " * string(typeof(desc))
        push!(var_defs, VarDef(name, typ, desc))
    end
    #escaping variables
    escapings = meta[2]
    for i = 1:length(escapings)
        name = escapings[i][1]
        typ  = escapings[i][2]
        desc = escapings[i][3]
        @assert (isa(name, Symbol)) "Expect local variable name to be Symbol, but got " * string(name)
        @assert (isa(typ, Type)) "Expect local variable type, but got " * string(typ)
        @assert (isa(desc, DescType)) "Expect local variable desc to be " * string(DescType) * " but got " * string(typeof(desc))
        push!(var_defs, VarDef(name, typ, desc))
        push!(escaping_vars, name)
    end
    #local GenSyms
    gensyms = meta[3]
    if isa(gensyms, Array)
        for i = 1:length(gensyms)
            typ = gensyms[i]
            desc = ISASSIGNED | ISASSIGNEDONCE
            id = i-1
            push!(var_defs, VarDef(typ, desc, id))
        end
    end
    static_params = length(meta) > 3 ? meta[3] : Any[]

    @assert (isa(lambda.args[3], Expr) && (lambda.args[3].head == :body)) "Expect a body Expr, but got " * string(lambda[3])
    return_typ = lambda.args[3].typ
    
    # we do not store original info
    new(input_params, vararg_params, escaping_vars, var_defs, static_params, return_typ, nothing)
  end
end

end

symbolToLHSVar(s :: Symbol, linfo :: LambdaVarInfo) = s

if VERSION >= v"0.5.0-dev+3875"

matchVarDef(x :: Symbol, vd :: VarDef) = vd.name == x
matchVarDef(x :: SlotNumber, vd :: VarDef) = vd.name != emptyVarName && vd.id == x.id
matchVarDef(x :: TypedSlot, vd :: VarDef) = vd.name != emptyVarName && vd.id == x.id
matchVarDef(x :: SSAValue, vd :: VarDef) = vd.name == emptyVarName && vd.id == x.id

toRHSVar(x :: Symbol, typ, linfo :: LambdaVarInfo) = toRHSVar(lookupLHSVarByName(x, linfo), linfo)
toRHSVar(x :: SlotNumber, typ, linfo :: LambdaVarInfo) = TypedSlot(x.id, typ)
toRHSVar(x :: TypedSlot, typ, linfo :: LambdaVarInfo) = x
toRHSVar(x :: SSAValue, typ, linfo :: LambdaVarInfo) = x
toRHSVar(vd :: VarDef) = vd.name == emptyVarName ? SSAValue(vd.id) : TypedSlot(vd.id, vd.typ)

toLHSVar(x :: Symbol, linfo :: LambdaVarInfo) = lookupLHSVarByName(x, linfo)
toLHSVar(x, linfo) = toLHSVar(x) 
toLHSVar(vd :: VarDef) = vd.name == emptyVarName ? SSAValue(vd.id) : SlotNumber(vd.id)

else

matchVarDef(x :: Symbol, vd :: VarDef) = vd.name == x
matchVarDef(x :: GenSym, vd :: VarDef) = vd.name == emptyVarName && vd.id == x.id

toRHSVar(x :: Symbol, typ, linfo :: LambdaVarInfo) = SymbolNode(x, typ)
toRHSVar(x :: SymbolNode, typ, linfo :: LambdaVarInfo) = x
toRHSVar(x :: GenSym, typ, linfo :: LambdaVarInfo) = x
toRHSVar(vd :: VarDef) = vd.name == emptyVarName ? GenSym(vd.id) : SymbolNode(vd.name, vd.typ)

toLHSVar(x, linfo) = toLHSVar(x) 
toLHSVar(vd :: VarDef) = vd.name == emptyVarName ? GenSym(vd.id) : vd.name
end

"""
Consolidate GenSym ids in LambdaVarInfo.
Return a dictionary to be used with replaceExprWithDict!(..)
"""
function consolidateLambdaVarInfo!(li::LambdaVarInfo)
    max_id = -1
    count  = Dict{Int,VarDef}()
    for vd in li.var_defs
        if vd.name == emptyVarName 
            if vd.id > max_id
                max_id = vd.id
            end
            count[vd.id] = vd
        end
    end
    dict = Dict{LHSVar,Any}()
    @assert (max_id + 1 >= length(count)) "duplicate entries in " * string(li)
    if max_id < 0 || max_id + 1 == length(count)
        return dict
    end
    # We preserve all ids that are less than count
    for i = 0:length(count)-1
        if !haskey(count, i)
            next_id = length(count)
            while next_id <= max_id
                if haskey(count, next_id) break end
                next_id = next_id + 1                
            end
            @assert (next_id <= max_id) "cannot find replacement GenSym for " * string(i)
            vd = count[next_id]
            vd.id = i
            count[i] = vd
            delete!(count, next_id)
            dict[GenSym(next_id)] = GenSym(i)
        end
    end
    @dprintln(3, "consolidateLambdaVarInfo! li=", li)
    @dprintln(3, "consolidateLambdaVarInfo! returns ", dict)
    return dict
end


function toRHSVar(x, linfo)
    return toRHSVar(x, getType(x, linfo), linfo)
end

"""
Pretty print a LambdaVarInfo.
"""
function show(io :: IO, li :: LambdaVarInfo)
  println(io, "Inputs = ")
  for x in li.input_params
    print(io, x)
    if in(x, li.vararg_params) 
      print(io, "...")
    end
    print(io, ", ")
  end
  println(io)
  if !isempty(li.static_parameter_names)
    println(io, "Static Parameter Names = ", li.static_parameter_names)
  end
  if !isempty(li.escaping_vars)
    println(io, "Escaping Variable Names = ", li.escaping_vars)
  end
  if li.return_type != nothing
    println(io, "Return type = ", li.return_type)
  end
  if !isempty(li.var_defs)
    println(io, "VarDefs")
    for i in li.var_defs
      println(io, "    ", i)
    end
  end
end

"""
Returns true if the given variable is an input parameter. 
"""
function isInputParameter(x::LHSVar, li :: LambdaVarInfo)
    name = nothing
    for vd in li.var_defs
        if matchVarDef(x, vd)
            name = vd.name
        end
    end
    return !is(name, nothing) && in(name, li.input_params)
end

"""
Return the (fresh copy of) input parameters as array of Symbols
"""
function getInputParameters(li :: LambdaVarInfo)
  return copy(li.input_params)
end

"""
Return the (fresh copy of) input parameters as array of Any, so vararg parameters are preserved.
"""
function getInputParametersAsExpr(li :: LambdaVarInfo)
  params = Array(Any, length(li.input_params))
  for i = 1:length(li.input_params)
    p = li.input_params[i]
    if in(p, li.vararg_params) 
      params[i] = Expr(:(::), p, Expr(:(...), Any))
    else
      params[i] = p
    end
  end
  return params
end

"""
Set the input parameters to be the given array of Symbols.
The caller has to ensure they are also added to locals in the LambdaVarInfo.
"""
function setInputParameters(params :: Array{Symbol, 1}, li :: LambdaVarInfo)
  li.input_params = copy(params) 
end

"""
Returns the type of a variable. 
"""
function getType(s::Union{Symbol,RHSVar}, li::LambdaVarInfo)
    x = toLHSVar(s,li)
    for vd in li.var_defs
        if matchVarDef(x, vd)
            return vd.typ
        end
    end
    error("Variable ", x, " is not found in ", li)
    #@dprintln(3, "Variable ", x, " is not found in ", li)
    #return Void
end

"""
Set the type for a local variable. 
"""
function setType(s :: Union{Symbol,RHSVar}, typ :: Type, li :: LambdaVarInfo)
    x = toLHSVar(s,li)
    for vd in li.var_defs
        if matchVarDef(x, vd)
            vd.typ = typ
            return 
        end
    end
    error("Variable ", x, " is not found in ", li)
end

"""
Returns the descriptor for a local variable. 
"""
function getDesc(s :: Union{Symbol,RHSVar}, li :: LambdaVarInfo)
    x = toLHSVar(s,li)
    for vd in li.var_defs
        if matchVarDef(x, vd)
            return vd.desc
        end
    end
    error("Variable ", x, " is not found in ", li)
end

"""
Set the descriptor for a local variable. 
"""
function setDesc(s :: Union{Symbol,RHSVar}, desc, li :: LambdaVarInfo)
    x = toLHSVar(s,li)
    for vd in li.var_defs
        if matchVarDef(x, vd)
            vd.desc = convert(DescType, desc)
            return
        end
    end
    error("Variable ", x, " is not found in ", li)
end

"""
Returns true if the given variable is a local variable (including input parameters, but exclude escaping variables). 
"""
function isLocalVariable(x::Union{Symbol,RHSVar}, li :: LambdaVarInfo)
    name = nothing
    for vd in li.var_defs
        if matchVarDef(x, vd)
            name = vd.name
        end
    end
    return name != nothing && !in(name, li.escaping_vars)
end

"""
Returns true if the given variable is an escaping variable. 
"""
function isEscapingVariable(s::Union{Symbol,RHSVar}, li :: LambdaVarInfo)
    x = isa(s, Symbol) ? s : toLHSVar(s,li)
    name = nothing
    for vd in li.var_defs
        if matchVarDef(x, vd)
            name = vd.name
        end
    end
    return name != nothing && in(name, li.escaping_vars)
end

"""
Returns an array of local variables and GenSyms, excluding escaping variables.
"""
function getLocalVariables(li :: LambdaVarInfo)
    locals = LHSVar[]
    for vd in li.var_defs
        if !in(vd.name, li.escaping_vars)
            push!(locals, toLHSVar(vd))
        end
    end
    return locals
end

"""
Returns an array of local variables and GenSyms, excluding escaping variables and parameters.
"""
function getLocalVariablesNoParam(li :: LambdaVarInfo)
    locals = LHSVar[]
    for vd in li.var_defs
        if !in(vd.name, li.escaping_vars) && !in(vd.name, li.input_params)
            push!(locals, toLHSVar(vd))
        end
    end
    return locals
end

"""
Returns the (fresh copy of) escaping variables as an array of Symbols.
"""
getEscapingVariables(li :: LambdaVarInfo) = copy(li.escaping_vars)
getEscapingVariablesAsLHSVar(li :: LambdaVarInfo) = map(x -> toLHSVar(x, li), li.escaping_vars)

"""
Adds a new local variable with the given Symbol "s", type "typ", descriptor "desc" in LambdaVarInfo "li".
Throw error if the variable has already existed. 
Return the newly added variable (RHSVar) as result.
"""
function addLocalVariable(s :: Symbol, typ :: Type, desc, li :: LambdaVarInfo)
    max_id = 0 
    for vd in li.var_defs
        if matchVarDef(s, vd)
            error("Variable ", s, " already exists in ", li)
        end
        if vd.name != emptyVarName && vd.id > max_id
            max_id = vd.id
        end
    end
    vd = VarDef(s, typ, convert(DescType, desc), max_id + 1)
    push!(li.var_defs, vd)
    return toRHSVar(vd)
end

"""
Add the given variable to be an escaping variable. Will error if 
the given variable already exists locally, or is a GenSym 
(or SSAValue in 0.5) or parameter.  Return true if it is not 
already escaping, or false otherwise.
"""
function addEscapingVariable(s :: Symbol, typ :: Type, desc, li :: LambdaVarInfo)
    x = addLocalVariable(s, typ, desc, li)
    setEscapingVariable(x, li)
end


"""
Set the given variable to be escaping. Will error if the given variable
doesn't already exist, or is a GenSym (or SSAValue in 0.5) or parameter.
Return true if it is not already escaping, or false otherwise.
"""
function setEscapingVariable(s :: Union{Symbol,RHSVar}, li :: LambdaVarInfo)
    x = toLHSVar(s,li)
    for vd in li.var_defs
        if matchVarDef(x, vd)
            @assert (vd.name != emptyVarName) "Variable " * string(x) * " does not have a Symbol name, and cannot be made escaping"
            @assert (!in(vd.name, li.input_params)) "Variable " * string(x) * " is an input parameter, and cannot be made escaping"
            if !in(vd.name, li.escaping_vars)
                push!(li.escaping_vars, vd.name)
                return true
            else
                return false
            end
        end
    end
    error("Variable ", x, " is not found in ", li)
end

"""
Set a local variable to be not escaping. Will error if the given variable
doesn't already exist, or is a GenSym (or SSAValue in 0.5) or parameter.
Return false if it is not already escaping, or true otherwise.
"""
function unsetEscapingVariable(s :: Union{Symbol,RHSVar}, li :: LambdaVarInfo)
    x = toLHSVar(s,li)
    for vd in li.var_defs
        if matchVarDef(x, vd)
            @assert (vd.name != emptyVarName) "Variable " * string(x) * " does not have a Symbol name, and cannot be made escaping"
            @assert (!in(vd.name, li.input_params)) "Variable " * string(x) * " is an input parameter, and cannot be made escaping"
            escapes = Symbol[]
            found = false
            for y in li.escaping_vars
                if y == vd.name 
                    found = true 
                else
                    push!(escaps, y) 
                end 
            end
            li.escaping_vars = found ? escapes : li.escaping_vars
            return found
        end
    end
    error("Variable ", x, " is not found in ", li)
end

"""
Add a new temporary (GenSym in 0.4 or SSAValue in 0.5) variable to the LambdaVarInfo. 
Returns the newly added variable. 
"""
function addTempVariable(typ, li :: LambdaVarInfo)
    max_id = -1
    for vd in li.var_defs
        if vd.name == emptyVarName && vd.id > max_id
            max_id = vd.id
        end
    end
    vd = VarDef(typ, convert(DescType, ISASSIGNEDONCE | ISASSIGNED), max_id + 1)
    push!(li.var_defs, vd)
    return toRHSVar(vd)
end

"""
Replace the symbols in an expression "expr" with those defined in the
dictionary "dict".  Return the result expression, which may share part of the
input expression, and the input "expr" may be modified inplace and shall not be used
after this call. 
"""
function replaceExprWithDict!(expr :: ANY, dict :: Dict{LHSVar, Any}, AstWalkFunc = nothing)
  function update_sym(expr :: ANY, dict, top_level_number :: Int64, is_top_level :: Bool, read :: Bool)
    if isfunctionhead(expr) 
        linfo, body = lambdaToLambdaVarInfo(expr)
        new_dict = Dict{LHSVar,Any}()
        for (k,v) in dict
            if !isLocalVariable(k, linfo) && isEscapingVariable(k, linfo)
                new_v = toLHSVar(v,linfo)
                if isa(new_v, Symbol) 
                    if !isLocalVariable(new_v, linfo)
                        @dprintln(3, "replaceExprWithDict! nested lambda replace ", k, " with ", v)
                        new_dict[k] = v
                        typ = getType(k, linfo)
                        desc = getDesc(k, linfo)
                        addEscapingVariable(new_v, typ, desc, linfo)
                    else
                        @dprintln(3, "replaceExprWithDict! nested lambda cannot replace ", k, " with ", v, " which is not Symbol")
                    end
                else
                    push!(new_dict, k, v)
                    @dprintln(3, "replaceExprWithDict! nested lambda replace ", k, " with ", v)
                end
            else
                @dprintln(3, "replaceExprWithDict! nested lambda skip replacing ", k, " because it is not escaping")
            end
        end
        replaceExprWithDict!(body, new_dict, AstWalkFunc)
        return expr
    elseif isa(expr, LHSVar)
      if haskey(dict, expr)
        return toLHSVar(dict[expr])
      end
    elseif isa(expr, TypedVar)
      lhsVar = toLHSVar(expr)
      if haskey(dict, lhsVar)
        return dict[lhsVar]
      end
    end
    return CompilerTools.AstWalker.ASTWALK_RECURSE
  end

  if expr == nothing
    return nothing
  end

  @dprintln(3, "replaceExprWithDict!: ", expr, " dict = ", dict, " AstWalkFunc = ", AstWalkFunc)
  if isa(expr,Array)
    for i = 1:length(expr)
      if AstWalkFunc == nothing
        expr[i] = CompilerTools.AstWalker.AstWalk(expr[i], update_sym, dict)
      else
        expr[i] = AstWalkFunc(expr[i], update_sym, dict)
      end
    end
  else
    if AstWalkFunc == nothing
      expr = CompilerTools.AstWalker.AstWalk(expr, update_sym, dict)
    else
      expr = AstWalkFunc(expr, update_sym, dict)
    end
  end
  return expr
end

"""
Merge "inner" LambdaVarInfo into "outer", and "outer" is changed as result.  Note
that the input_params, static_parameter_names, and escaping_defs of "outer" do
not change, other fields are merged. The GenSyms in "inner" will need to adjust
their indices as a result of this merge. We return a dictionary that maps from
old GenSym to new GenSym for "inner", which can be used to adjust the body Expr
of "inner" lambda using "replaceExprWithDict" or "replaceExprWithDict!".
"""
function mergeLambdaVarInfo(outer :: LambdaVarInfo, inner :: LambdaVarInfo)
    dict = Dict{LHSVar, Any}()
    @dprintln(3,"outer = ", outer)
    @dprintln(3,"inner = ", inner)
    for vd in inner.var_defs
        if vd.name == emptyVarName  
            # temporary var, add to outer
            dict[toLHSVar(vd)] = addTempVariable(vd.typ, outer)
        else
            # named var
            # first, all input parameters are skipped
            name = vd.name
            typ  = vd.typ
            desc = vd.desc
            if !in(name, inner.input_params)
                if in(name, inner.escaping_vars)
                    # if escaping, must exist as variable in outer
                    @assert (isLocalVariable(name, outer) || isEscapingVariable(name, outer)) "Variable " * string(vd.name) * " is not found in outer info " * string(outer)
                    # clear ISCAPTURED and ISASSIGNEDBYINNERFUNCTION is not correct since this variable could still be escaping in other context
                    # desc = desc & (~ ISASSIGNEDBYINNERFUNCTION)
                    # desc = desc & (~ ISCAPTURED)
                    # setDesc(name, desc, outer)
                    # must replace escaping variables too, because the actual variable representation would be different in 0.5 between outer and inner
                    dict[toLHSVar(vd)] = toRHSVar(lookupLHSVarByName(name, outer), outer)
                else
                    # fresh name if there is name conflict
                    if isLocalVariable(name, outer) || isEscapingVariable(name, outer)
                        name = gensym(string(name)) 
                    end
                    dict[toLHSVar(vd)] = addLocalVariable(name, typ, desc, outer)
                end
            end
        end
    end
    return dict
end

function lambdaToLambdaVarInfo(lambda :: LambdaInfo)
    ast = Base.uncompressed_ast(lambda)
    linfo = LambdaVarInfo(lambda, ast)
    body = getBody(ast, linfo.return_type)
    return linfo, body
end

function lambdaToLambdaVarInfo(lambda :: Expr)
    @assert (lambda.head == :lambda) "Expect a :lambda Expr, but got " * string(lambda)
    linfo = LambdaVarInfo(lambda)
    body = getBody(lambda)
    return linfo, body
end

"""
Returns the type of the lambda as stored in LambdaVarInfo "li" and as extracted during lambdaToLambdaVarInfo.
"""
function getReturnType(li :: LambdaVarInfo)
  return li.return_type
end

"""
set the return type of LambdaVarInfo "li".
"""
function setReturnType(ret_typ, li :: LambdaVarInfo)
  @assert (ret_typ != nothing)
  li.return_type = ret_typ
end

if VERSION > v"0.5.0-dev+3260"
function lambdaTypeinf(lambda :: LambdaInfo, typs; optimize = true)
    throw(string("Force inference LambdaInfo in 0.5 not yet supported"))
end
else
"""
Force type inference on a LambdaStaticData object.
Return both the inferred AST that is to a "code_typed(Function, (type,...))" call, 
and the inferred return type of the input method.
"""
function lambdaTypeinf(lambda :: LambdaStaticData, typs; optimize = true)
  types::Any = to_tuple_type(Tuple{typs...})
  (tree, ty) = Core.Inference.typeinf_uncached(lambda, types, Core.svec(), optimize = optimize)
  lambda.ast = tree
  return lambda, ty
end
end

function lambdaTypeinf(ftyp :: Type, typs; optimize = true)
    types::Any = to_tuple_type(Tuple{ftyp, typs...})
    env = Core.Inference.svec()
#    println("lambdaTypeinf typeof(ftyp) = ", typeof(ftyp))
#    println("lambdaTypeinf typeof(ftyp.name) = ", typeof(ftyp.name))
#    println("lambdaTypeinf typeof(ftyp.name.mt) = ", typeof(ftyp.name.mt))
#    println("lambdaTypeinf typeof(ftyp.name.mt.defs) = ", typeof(ftyp.name.mt.defs))
#    println("ftyp = ", ftyp)
#    println("ftyp.name = ", ftyp.name)
#    println("ftyp.name.mt = ", ftyp.name.mt)
#    println("ftyp.name.mt.defs = ", ftyp.name.mt.defs)
if VERSION > v"0.5.0-dev+3260"
    println("ftyp = ", ftyp, " typs = ", typs, " methods = ", Base.methods(ftyp))
#    meth = Base._methods(ftyp, typs, -1)
#    if length(meth) == 1
#        println("meth in _methods ", meth)
#        meth = meth[1]
        
        lambda = Core.Inference.func_for_method_checked(ftyp.name.mt.defs.func, types)
        (tree, ty) = Core.Inference.typeinf_uncached(lambda, types, Core.svec(), optimize = optimize)
#        println("lambdaTypeinf typeof(tree) = ", typeof(tree), " typeof(ty) = ", typeof(ty))
        return tree, ty
#    else
#        error("Expected one method from call to Base._methods in lambdaTypeinf, but got ", meth)
#    end
else
    lambda = Core.Inference.func_for_method(ftyp.name.mt.defs, typs, env)
#    println("lambdaTypeinf typeof(lambda) = ", typeof(lambda))
    (tree, ty) = Core.Inference.typeinf_uncached(lambda, types, Core.svec(), optimize = optimize)
#    println("lambdaTypeinf typeof(tree) = ", typeof(tree), " typeof(ty) = ", typeof(ty))
    lambda.ast = tree
    return lambda, ty
end
end

if VERSION > v"0.5.0-dev+3260"
function LambdaVarInfoToLambda(li :: LambdaVarInfo, body::Array{Any,1}, AstWalkFunc = nothing)
    @assert (length(li.escaping_vars)==0) "LambdaVarInfo has escaping variables, and cannot be converted back to LambdaInfo " * string(li)
    lambda = li.orig_info
    @assert (lambda != nothing) "li.orig_info is not found " * string(li)
    @dprintln(3, "LambdaVarInfoToLambda, LambdaVarInfo = ", li, " body = ", body)
    nparams = length(li.input_params)
    dict = Dict{LHSVar,Any}()
    vars = Any[nothing for i = 1:length(li.var_defs)]
    ssas = Any[nothing for i = 1:length(li.var_defs)]
    vars_pending = VarDef[]
    ssas_pending = VarDef[]
    # parameters come first
    nvars = 0
    nssas = 0
    for vd in li.var_defs
      if vd.name == Symbol("#self#")
        assert(vars[1] == nothing)
        vars[1] = vd
        nvars += 1
      elseif vd.name != emptyVarName
        nvars += 1
        j = findfirst(li.input_params, vd.name)
        if j > 0
          # parameter
          assert(vars[j + 1] == nothing) 
          vars[j+1] = vd
        else
          # non-parameter variable
          if vd.id <= nparams + 1 && vars[vd.id] == nothing
            vars[vd.id] = vd
          else # place already taken
            push!(vars_pending, vd)
          end
        end
      else # ssavalues
        nssas += 1
        if ssas[vd.id+1] == nothing
          ssas[vd.id+1] = vd
        else
          push!(ssas_pending, vd)
        end
      end
    end
    lambda.slotnames = Array(Any, nvars)
    lambda.slottypes = Array(Any, nvars)
    lambda.slotflags = Array(DescType, nvars)
    @dprintln(3, "nvars = ", nvars)
    @dprintln(3, "vars = ", vars)
    @dprintln(3, "vars_pending = ", vars_pending)
    @dprintln(3, "ssas = ", ssas)
    @dprintln(3, "ssas_pending = ", ssas_pending)
    j = 1
    for i = 1:nvars
      if vars[i] == nothing
        assert(j <= length(vars_pending))
        vars[i] = vars_pending[j]
        j += 1
      end
      vd = vars[i]
      if vd.id != i
        # id mismatch, must replace
        dict[toLHSVar(vd)] = TypedSlot(i, vd.typ)
        vd.id = i
      end
      li.var_defs[i] = vd
      lambda.slotnames[i] = vd.name
      lambda.slottypes[i] = vd.typ
      lambda.slotflags[i] = vd.desc
    end
    @dprintln(3, "lambda.nargs = ", lambda.nargs, " nparams = ", nparams)
    lambda.nargs = nparams + 1
    lambda.ssavaluetypes = Array(Type, nssas)
    j = 1
    for i = 1:nssas
      if ssas[i] == nothing
        assert(j <= length(ssas_pending))
        ssas[i] = ssas_pending[j]
        j += 1
      end
      vd = ssas[i]
      if vd.id != i - 1
        dict[toLHSVar(vd)] = GenSym(i - 1)
        vd.id = i - 1
      end
      li.var_defs[nvars + i] = vd
      lambda.ssavaluetypes[i] = vd.typ
    end
    lambda.rettype = li.return_type
    body = replaceExprWithDict!(body, dict, AstWalkFunc)
    lambda.code =  ccall(:jl_compress_ast, Any, (Any,Any), lambda, body)
    @dprintln(3, "lambda.slotnames = ", lambda.slotnames)
    @dprintln(3, "lambda.slottypes = ", lambda.slottypes)
    @dprintln(3, "lambda.slotflags = ", lambda.slotflags)
    @dprintln(3, "lambda.ssavaluetypes = ", lambda.ssavaluetypes)
    @dprintln(3, "LambdaVarInfoToLambda, lambda = ", lambda)
    return lambda
end

else # if VERSION

function createMeta(li::LambdaVarInfo)
    locals = Any[]
    escapes = Any[]
    max_id = -1
    count = 0
    for vd in li.var_defs
        if vd.name == emptyVarName && vd.id > max_id
            max_id = vd.id
            count+=1
        end
    end
    gensyms = Array(Any, max_id + 1)
    for vd in li.var_defs
        if vd.name == emptyVarName
            gensyms[vd.id + 1] = vd.typ
        elseif in(vd.name, li.escaping_vars)
            push!(escapes, Any[vd.name, vd.typ, vd.desc])
        else
            push!(locals, Any[vd.name, vd.typ, vd.desc])
        end
    end 
    meta = Any[locals, escapes, gensyms]
    if isa(li.static_parameter_names, Array)
        push!(meta, li.static_parameter_names)
    end
    return meta
end

"""
Convert our internal storage format, LambdaVarInfo, back into a lambda expression.
This takes a LambdaVarInfo and a body as input parameters.
This body can be a body expression or you can pass "nothing" if you want but then you will probably need to set the body in args[3] manually by yourself.
"""
function LambdaVarInfoToLambda(li :: LambdaVarInfo, body::Array{Any,1}, AstWalkFunc = nothing)
  expr = Expr(:body)
  expr.args = body
  if li.return_type != nothing
      expr.typ = li.return_type
  end
  return Expr(:lambda, getInputParametersAsExpr(li), createMeta(li), expr)
end

end # if VERSION

function LambdaVarInfoToLambda(li :: LambdaVarInfo, body_expr :: Expr, AstWalkFunc = nothing)
  assert(body_expr.head == :body)
  LambdaVarInfoToLambda(li, body_expr.args, AstWalkFunc)
end

"""
Update the descriptor part of the VarDef dealing with whether the variable is assigned or not in the function.
Takes the LambdaVarInfo and a dictionary that maps symbols names to the number of times they are statically assigned in the function.
"""
function updateAssignedDesc(li :: LambdaVarInfo, symbol_assigns :: Dict{Symbol,Int})
  # For each VarDef
  for vd in li.var_defs
    # If that VarDef's symbol is in the dictionary.
    if vd.name != emptyVarName && haskey(symbol_assigns, vd.name)
      # Get how many times the symbol is assigned to.
      num_assigns = symbol_assigns[vd.name]
      # Remove the parts of the descriptor dealing with the number of assignments.
      vd.desc = vd.desc & (~ (ISASSIGNED | ISASSIGNEDONCE)) 
      if num_assigns > 1
        # If more than one assignment then OR on ISASSIGNED.
        vd.desc = vd.desc | ISASSIGNED
      elseif num_assigns == 1
        # If exactly one assignment then OR on ISASSIGNED and ISASSIGNEDONCE
        vd.desc = vd.desc | ISASSIGNED | ISASSIGNEDONCE
      end
    end
  end
end

if VERSION > v"0.5.0-dev+3260"
function getBody(lambda :: LambdaInfo)
  return getBody(Base.uncompressed_ast(lambda), lambda.rettype)
end
else
function getBody(lambda :: LambdaStaticData)
  return getBody(Base.uncompressed_ast(lambda))
end
end

function getBody(lambda :: Expr, rettype = nothing)
  assert(lambda.head == :lambda)
  body = lambda.args[3]
  if rettype != nothing
    body.typ = rettype
  end
  return body
end

function getBody(lambda :: Array{Any,1}, rettype)
  body = Expr(:body)
  body.args = lambda
  body.typ = rettype
  return body
end

function prependStatements(body :: Expr, stmts:: Array{Any, 1})
  assert(body.head == :body)
  body.args = [stmts; body.args]
  return body
end

"""
Returns an array of Symbols corresponding to those parameters to the method that are going to be passed by reference.
In short, isbits() types are passed by value and !isbits() types are passed by reference.
"""
function getRefParams(li :: LambdaVarInfo)
  ret = LHSVar[]

  for x in li.input_params
    typ = getType(x, li)
    @dprintln(3,"x = ", x, " type = ", typ)
    if !isbits(typ)
        push!(ret, lookupLHSVarByName(x, li))
    end
  end

  return ret
end

function getArrayParams(li :: LambdaVarInfo)
  ret = LHSVar[]

  input_vars = li.input_params
  var_types  = li.var_defs

  for x in li.input_params
      typ = getType(x, li)
      if isArrayType(typ)
        push!(ret, lookupLHSVarByName(x, li))
      end
  end

  return ret
end

"""
Get the name of a local variable, either as Symbol or GenSym
"""
function lookupVariableName(s::Union{Symbol,RHSVar}, li::LambdaVarInfo) 
    x = toLHSVar(s, li)
    for vd in li.var_defs
        if matchVarDef(x, vd)
            return vd.name == emptyVarName ? toLHSVar(vd) : vd.name
        end
    end
    error("Variable ", s, " is not found in ", li)
end

"""
Lookup a Symbol in local variables, and return that variable (as LHSVar).
"""
function lookupLHSVarByName(s::Symbol, li::LambdaVarInfo)
    for vd in li.var_defs
        if matchVarDef(s, vd)
            return toLHSVar(vd)
        end
    end
    error("Variable ", s, " is not found in ", li)
end

"""
Holds symbols and gensyms that are seen in a given AST when using the specified callback to handle non-standard Julia AST types.
"""
type CountVariableState
  used :: Set{LHSVar}

  function CountVariableState()
    new(Set{LHSVar}())
  end
end

"""
Adds symbols and gensyms to their corresponding sets in CountSymbolState when they are seen in the AST.
"""
function count_variables(x::RHSVar,
                       state::CountVariableState,
                       top_level_number,
                       is_top_level,
                       read)
    push!(state.used, toLHSVar(x))
    return CompilerTools.AstWalker.ASTWALK_RECURSE
end

function count_variables(x::ANY,
                       state::CountVariableState,
                       top_level_number,
                       is_top_level,
                       read)
    return CompilerTools.AstWalker.ASTWALK_RECURSE
end

function countVariables(body, AstWalkFunc = nothing)
  css = CountVariableState()
  if AstWalkFunc == nothing
    CompilerTools.AstWalker.AstWalk(body, count_variables, css)
  else
    AstWalkFunc(body, count_variables, css)
  end
  return css.used
end

"""
Eliminates unused symbols from the LambdaVarInfo var_defs.
Takes a LambdaVarInfo to modify, the body to scan using AstWalk and an optional callback to AstWalk for custom AST types.
"""
function eliminateUnusedLocals!(li :: LambdaVarInfo, body, AstWalkFunc = nothing)
  used = countVariables(body, AstWalkFunc)
  @dprintln(3,"used = ", used)
  var_defs = VarDef[]
  for vd in li.var_defs
    if !in(vd.name, li.input_params) && vd.name != Symbol("#self#")
      lhsVar = toLHSVar(vd)
      if !in(lhsVar, used) continue end
    end
    push!(var_defs, vd)
  end
  li.var_defs = var_defs
  dict = consolidateLambdaVarInfo!(li)
  @dprintln(3,"dict = ", dict)
  body = replaceExprWithDict!(body, dict, AstWalkFunc)
  @dprintln(3,"updated body = ", body)
  return body
end



end
