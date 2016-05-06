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
using CompilerTools.AstWalker
using Core.Inference: to_tuple_type

import Base.show

export VarDef, LambdaVarInfo, toRHSVar, symbolToLHSVar, prependStatements
export getDesc, getType, getVarDef, isInputParameter, isLocalVariable, isEscapingVariable, isLocalGenSym, getTypedVar
export getParamsNoSelf, setParamsNoSelf, addInputParameter, addLocalVariable, addEscapingVariable, addGenSym, deleteEscapingVariable
export parameterToSymbol, getLocalNoParams, getLocals, getEscapingVariables, getVariableName
export getBody, getReturnType, setReturnType
export lambdaToLambdaVarInfo, LambdaVarInfoToLambda, updateTypedVar, getSymbol, genWithRename
if VERSION > v"0.5.0-dev+3260"
#export LambdaVarInfoToLambdaInfo
export slotToSym
end
export getRefParams, updateType, updateAssignedDesc, lambdaTypeinf, replaceExprWithDict, replaceExprWithDict!
export ISCAPTURED, ISASSIGNED, ISASSIGNEDBYINNERFUNCTION, ISCONST, ISASSIGNEDONCE 

# Possible values of VarDef descriptor that can be OR'ed together.
const ISCAPTURED = 1
const ISASSIGNED = 2
const ISASSIGNEDBYINNERFUNCTION = 4
const ISCONST = 8
const ISASSIGNEDONCE = 16

if VERSION > v"0.5.0-dev+3260"

"""
Represents the triple stored in a lambda's args[2][1].
The triple is 1) the Symbol of an input parameter or local variable, 2) the type of that Symbol, and 3) a descriptor for that symbol.
The descriptor can be 0 if the variable is an input parameter, 1 if it is captured, 2 if it is assigned within the function, 4 if
it is assigned by an inner function, 8 if it is const, and 16 if it is assigned to statically only once by the function.
"""
type VarDef
  name :: Symbol
  typ  :: DataType
  desc :: UInt8
  id   :: Int

  function VarDef(n, t, d, i)
    new(n, t, d, i)
  end
end


type LambdaVarInfo
  input_params  :: Array{Any,1}
  var_defs      :: Dict{Symbol,VarDef}
  gen_sym_typs  :: Array{Any,1}
  escaping_defs :: Dict{Symbol,VarDef}
  static_parameter_names :: Array{Any,1}
  return_type   :: Any
  orig_info     :: Union{LambdaInfo,Void}

  function LambdaVarInfo()
    new(Any[], Dict{Symbol,VarDef}(), Any[], Dict{Symbol,VarDef}(), Any[], Void, nothing)
  end

  function LambdaVarInfo(li::LambdaVarInfo)
    new(copy(li.input_params), copy(li.var_defs), copy(li.gen_sym_typs), copy(li.escaping_defs), copy(li.static_parameter_names), copy(li.return_type), copy(li.orig_info))
  end

  function LambdaVarInfo(li::LambdaInfo)
    new(Any[], Dict{Symbol,VarDef}(), Any[], Dict{Symbol,VarDef}(), Any[], Void, li)
  end
end

symbolToLHSVar(s :: Symbol, linfo :: LambdaVarInfo) = SlotNumber(linfo.var_defs[s].id)

function getTypedVar(s :: Symbol, t, linfo :: LambdaVarInfo)
  var_def = linfo.var_defs[s]
  TypedSlot(var_def.id, t) 
end

function toRHSVar(x :: Symbol, typ, linfo :: LambdaVarInfo)
  return getTypedVar(x, typ, linfo)
end

function toRHSVar(x :: TypedVar, typ, linfo :: LambdaVarInfo)
  return x
end

function toRHSVar(x :: GenSym, typ, linfo :: LambdaVarInfo)
  return x
end

function toRHSVar(x, typ, linfo :: LambdaVarInfo)
  xtyp = typeof(x)
  throw(string("Found object type ", xtyp, " for object ", x, " in toRHSVar and don't know what to do with it."))
end

symbolToSlotId(s::Symbol, linfo :: LambdaVarInfo) = linfo.var_defs[s].id

function updateTypedVar(tv::TypedVar, s::Symbol, linfo :: LambdaVarInfo)
  tv.id = symbolToSlotId(s)
  return tv
end

getSymbol(s :: TypedVar, linfo :: LambdaVarInfo) = slotToSym(s, linfo)
getSymbol(s :: SlotNumber, linfo :: LambdaVarInfo) = slotToSym(s, linfo)

else

"""
Represents the triple stored in a lambda's args[2][1].
The triple is 1) the Symbol of an input parameter or local variable, 2) the type of that Symbol, and 3) a descriptor for that symbol.
The descriptor can be 0 if the variable is an input parameter, 1 if it is captured, 2 if it is assigned within the function, 4 if
it is assigned by an inner function, 8 if it is const, and 16 if it is assigned to statically only once by the function.
"""
type VarDef
  name :: Symbol
  typ  :: DataType
  desc :: Int64

  function VarDef(n, t, d)
    new(n, t, d)
  end
end


"""
An internal format for storing a lambda expression's args[1] and args[2].
The input parameters are stored as a Set since they must be unique and it makes for faster searching.
The VarDefs are stored as a dictionary from symbol to VarDef since type lookups are reasonably frequent and need to be fast.
The GenSym part (args[2][3]) is stored as an array since GenSym's are indexed.
Captured_outer_vars and static_parameter_names are stored as arrays for now since we don't expect them to be changed much.
"""
type LambdaVarInfo
  input_params  :: Array{Any,1}
  var_defs      :: Dict{Symbol,VarDef}
  gen_sym_typs  :: Array{Any,1}
  escaping_defs :: Dict{Symbol,VarDef}
  static_parameter_names :: Array{Any,1}
  return_type   :: Any
  orig_info     :: Union{Expr,Void}

  function LambdaVarInfo()
    new(Any[], Dict{Symbol,VarDef}(), Any[], Dict{Symbol,VarDef}(), Any[], Void, nothing)
  end

  function LambdaVarInfo(li::LambdaVarInfo)
    new(copy(li.input_params), copy(li.var_defs), copy(li.gen_sym_typs), copy(li.escaping_defs), copy(li.static_parameter_names), copy(li.return_type), deepcopy(li.orig_info))
  end

  function LambdaVarInfo(li :: Expr)
    new(Any[], Dict{Symbol,VarDef}(), Any[], Dict{Symbol,VarDef}(), Any[], Void, li)
  end
end

symbolToLHSVar(s :: Symbol, linfo :: LambdaVarInfo) = s

function getTypedVar(s :: Symbol, t, linfo :: LambdaVarInfo)
  SymbolNode(s, t)
end

function toRHSVar(x :: Symbol, typ, linfo :: LambdaVarInfo)
    return SymbolNode(x, typ)
end

function toRHSVar(x :: SymbolNode, typ, linfo :: LambdaVarInfo)
    return x
end

function toRHSVar(x :: GenSym, typ, linfo :: LambdaVarInfo)
    return x
end

function toRHSVar(x, typ, linfo :: LambdaVarInfo)
    xtyp = typeof(x)
    throw(string("Found object type ", xtyp, " for object ", x, " in toRHSVar and don't know what to do with it."))
end

function updateTypedVar(tv::TypedVar, s::Symbol, linfo :: LambdaVarInfo)
    tv.name = s
    return tv
end

getSymbol(s :: TypedVar, linfo :: LambdaVarInfo) = s.name

end

getSymbol(s :: Symbol, linfo :: LambdaVarInfo) = s
getSymbol(s :: GenSym, linfo :: LambdaVarInfo) = s
function getSymbol(s :: Expr, linfo :: LambdaVarInfo)
    @dprintln(0, "ssn.head = ", ssn.head)
    assert(ssn.head == :(::))
    return ssn.args[1]
end

"""
Pretty print a LambdaVarInfo.
"""
function show(io :: IO, li :: LambdaVarInfo)
  println(io, "Inputs = ", li.input_params)
  if !isempty(li.static_parameter_names)
    println(io, "Static Parameter Names = ", li.static_parameter_names)
  end
  if li.return_type != nothing
    println(io, "Return type = ", li.return_type)
  end
  if !isempty(li.var_defs)
    println(io, "VarDefs")
    for i in li.var_defs
      println(io, "    ", i[2])
    end
  end
  if !isempty(li.gen_sym_typs)
    println(io, "GenSym")
    for i = 1:length(li.gen_sym_typs)
      println(io, "    ", i-1, " => ", li.gen_sym_typs[i])
    end
  end
  if !isempty(li.escaping_defs)
    println(io, "EscapingDefs")
    for i in li.escaping_defs
      println(io, "    ", i[2])
    end
  end
end

"""
Holds symbols and gensyms that are seen in a given AST when using the specified callback to handle non-standard Julia AST types.
"""
type CountSymbolState
  used_symbols :: Set{Symbol}
  used_gensyms :: Set{Int64}

  function CountSymbolState()
    new(Set{Symbol}(), Set{Int64}())
  end
end

"""
Adds symbols and gensyms to their corresponding sets in CountSymbolState when they are seen in the AST.
"""
function count_symbols(x::Symbol,
                       state::CountSymbolState,
                       top_level_number,
                       is_top_level,
                       read)
    push!(state.used_symbols, x)
    return CompilerTools.AstWalker.ASTWALK_RECURSE
end

function count_symbols(x::TypedVar,
                       state::CountSymbolState,
                       top_level_number,
                       is_top_level,
                       read)
    push!(state.used_symbols, toLHSVar(x))
    return CompilerTools.AstWalker.ASTWALK_RECURSE
end

function count_symbols(x::GenSym,
                       state::CountSymbolState,
                       top_level_number,
                       is_top_level,
                       read)
    push!(state.used_gensyms, x.id)
    return CompilerTools.AstWalker.ASTWALK_RECURSE
end

function count_symbols(x::ANY,
                       state::CountSymbolState,
                       top_level_number,
                       is_top_level,
                       read)
    return CompilerTools.AstWalker.ASTWALK_RECURSE
end

"""
Eliminates unused symbols from the LambdaVarInfo var_defs.
Takes a LambdaVarInfo to modify, the body to scan using AstWalk and an optional callback to AstWalk for custom AST types.
"""
function eliminateUnusedLocals!(li :: LambdaVarInfo, body, AstWalkFunc = nothing)
  css = CountSymbolState()
  if AstWalkFunc == nothing
    CompilerTools.AstWalker.AstWalk(body, count_symbols, css)
  else
    AstWalkFunc(body, count_symbols, css)
  end
  @dprintln(3,"css = ", css)
  for i in li.var_defs
    if isInputParameter(i[1], li)
      continue
    end
    if !in(i[1], css.used_symbols)
      delete!(li.var_defs, i[1])
    end
  end

  gensymdict = Dict{LHSVar,Any}()
  newgensym  = Any[]
  next_id    = 0
  for i = 0:length(li.gen_sym_typs)-1
    if in(i, css.used_gensyms)
      push!(newgensym, li.gen_sym_typs[i+1])
      gensymdict[GenSym(i)] = GenSym(next_id)
      next_id = next_id + 1
    end
  end
  @dprintln(3,"gensymdict = ", gensymdict)
  @dprintln(3,"newgensym = ", newgensym)
  li.gen_sym_typs = newgensym
  body = replaceExprWithDict!(body, gensymdict, AstWalkFunc)
  @dprintln(3,"updated body = ", body)
  return body
end

function getInputParameters(li :: LambdaVarInfo)
  return li.input_params
end

"""
Add Symbol "v" as input parameter to LambdaVarInfo "li".
"""
function addInputParameter(v::Symbol, ty, desc, li :: LambdaVarInfo)
  push!(li.input_params, v)
  addLocalVariable(v, ty, desc, li)
end

"""
Add VarDef "vd" as input parameter to LambdaVarInfo "li".
"""
function addInputParameter(vd :: VarDef, li :: LambdaVarInfo)
  push!(li.input_params, vd.name)
  addLocalVariable(vd, li)
end

"""
Add all variable in "collection" as input parameters to LambdaVarInfo "li".
"""
function addInputParameters(collection, li :: LambdaVarInfo)
  for i in collection
    addInputParameter(i, li)
  end
end

"""
Get the input parmeters as an array. Note that for Julia 0.5 we filter out
the #self# parameter if it is present.
"""
function getParamsNoSelf(li::LambdaVarInfo)
  params = li.input_params
  if length(params) > 0 && params[1] == Symbol("#self#")
    return params[2:end]
  else
    return params
  end
end

"""
Set the input parmeters to the given array without changing local
variable table. Note that for Julia 0.5 we will insert a #self# 
parameter to the actual parameter list. 
"""
function setParamsNoSelf(new_params::Array{Any,1}, li::LambdaVarInfo)
  params = li.input_params
  if length(params) > 0 && params[1] == Symbol("#self#")
    li.input_params = vcat(Any[params[1]], new_params)
  else
    li.input_params = copy(new_params)
  end
end

"""
Returns the type of a Symbol or GenSym in "x" from LambdaVarInfo in "li".
"""
function getType(x::Symbol, li::LambdaVarInfo)
    if haskey(li.var_defs, x) li.var_defs[x].typ
    elseif haskey(li.escaping_defs, x) li.escaping_defs[x].typ
    else 
        res = eval(x)
        res_typ = typeof(res)
        @dprintln(3, "getType Symbol x = ", x, " eval(x) = ", res, " typeof(res) = ", res_typ)
        if res_typ == DataType
            return res_typ
        else
            throw(string("getType called with ", x, " which is not found in LambdaVarInfo: ", li))
        end
    end
end

function getType(x::GenSym, li::LambdaVarInfo)
    return li.gen_sym_typs[x.id + 1]
end

if VERSION > v"0.5.0-dev+3260"
slotToSym(x::TypedSlot, li::LambdaVarInfo)  = li.orig_info.slotnames[x.id]
slotToSym(x::SlotNumber, li::LambdaVarInfo) = li.orig_info.slotnames[x.id]

function getType(x::SlotNumber, li::LambdaVarInfo)
    @dprintln(3,"getType for Slot, x = ", x)
    return li.orig_info.slottypes[x.id]
end

function getType(x::TypedSlot, li::LambdaVarInfo)
    @dprintln(3,"getType for TypedSlot, x = ", x)
    if x.typ == Any
        return li.orig_info.slottypes[x.id]
    else
        return x.typ
    end
end
else
function getType(x::SymbolNode, li::LambdaVarInfo)
    return x.typ
end
end
function getType(x::Any, li::LambdaVarInfo)
    throw(string("getType called with neither Symbol or GenSym input.  Instead the input was ", x, " of type ", typeof(x)))
end

#- The following are not related to variables, and should be taken care of by the caller
function getType(x::Expr, li::LambdaVarInfo)
    return x.typ
end

function getType(x::Union{GlobalRef,QuoteNode}, li::LambdaVarInfo)
    return typeof(eval(x))
end

function getType(x::Union{Number,DataType}, li::LambdaVarInfo)
    return typeof(x)
end

if VERSION > v"0.5.0-dev+3260"
function getType(x::LambdaInfo, li::LambdaVarInfo)
    return typeof(x)
end
else
function getType(x::LambdaStaticData, li::LambdaVarInfo)
    return typeof(x)
end
end
-#

function updateType(li::LambdaVarInfo, x::Symbol, typ)
    if haskey(li.var_defs, x)
        li.var_defs[x].typ = typ
    elseif haskey(li.escaping_defs, x)
        @dprintln(3, "updateType: cannot update type of escaping variable", x)
    else
        throw(string("updateType: cannot update the type of ", x, " because it is not a local variable"))
    end
    return nothing
end

function updateType(li::LambdaVarInfo, x::GenSym, typ)
    @assert (x.id >= 0 && x.id < length(li.gen_sym_typs)) ("cannot update the type of " * string(x) * " because it is not a local GenSym")
    li.gen_sym_typs[x.id + 1] = typ
    return nothing
end

updateType(li::LambdaVarInfo, x::TypedVar, typ) = updateType(li, toLHSVar(x), typ)

function updateType(li::LambdaVarInfo, x, typ)
    throw(string("updateType called with neither Symbol or GenSym input.  Instead the input type was ", typeof(x)))
end

"""
Returns the descriptor for a local variable or input parameter "x" from LambdaVarInfo in "li".
"""
function getDesc(x :: Symbol, li :: LambdaVarInfo)
    if haskey(li.var_defs, x) li.var_defs[x].desc
    elseif haskey(li.escaping_defs, x) li.escaping_defs[x].desc
    else 
      throw(string("getDesc called with unfound variable ", x))
    end
end

function getDesc(x :: TypedVar, li :: LambdaVarInfo)
    getDesc(toLHSVar(x), li)
end

function getDesc(x :: GenSym, li :: LambdaVarInfo)
  return ISASSIGNED | ISASSIGNEDONCE
end

"""
Returns the VarDef for a Symbol in LambdaVarInfo in "li"
"""
function getVarDef(s :: Symbol, li :: LambdaVarInfo)
  return li.var_defs[s]
end

"""
Returns true if the Symbol in "s" is an input parameter in LambdaVarInfo in "li".
"""
function isInputParameter(s :: Symbol, li :: LambdaVarInfo)
    for p in li.input_params
        if (isa(p, Symbol) && p == s) || 
           (isa(p, Expr) && p.args[1] == s) || 
           (isa(p, TypeVar) && p.name == s)
            return true
        end
    end
    return false
end

function isInputParameter(s::GenSym, li::LambdaVarInfo)
    return false
end

if VERSION > v"0.5.0-dev+3260"
function isInputParameter(s :: SlotNumber, li :: LambdaVarInfo)
    isInputParameter(slotToSym(s,li), li)
end
end

"""
Returns true if the Symbol in "s" is a local variable in LambdaVarInfo in "li".
"""
function isLocalVariable(s :: Symbol, li :: LambdaVarInfo)
  return haskey(li.var_defs, s) && !isInputParameter(s, li)
end

if VERSION > v"0.5.0-dev+3260"
"""
Returns an array of local variables and GenSyms.
"""
function getLocals(li :: LambdaVarInfo)
  locals = Any[]
  for k in li.var_defs
      push!(locals, SlotNumber(k[2].id))
  end
  for i in 1:length(li.gen_sym_typs)
      push!(locals, GenSym(i-1))
  end
  return locals
end

"""
Returns an array of local variables and GenSyms, excluding parameters.
"""
function getLocalNoParams(li :: LambdaVarInfo)
  locals = Any[]
  for k in li.var_defs
    if !isInputParameter(k[1], li)
        push!(locals, k[1])
    end
  end
  for i in 1:length(li.gen_sym_typs)
      push!(locals, GenSym(i-1))
  end
  return locals
end

else

"""
Returns an array of local variables and GenSyms.
"""
function getLocals(li :: LambdaVarInfo)
  locals = Any[]
  for k in keys(li.var_defs)
      push!(locals, k)
  end
  for i in 1:length(li.gen_sym_typs)
      push!(locals, GenSym(i-1))
  end
  return locals
end

"""
Returns an array of local variables and GenSyms, excluding parameters
"""
function getLocalNoParams(li :: LambdaVarInfo)
  locals = Any[]
  for k in keys(li.var_defs)
    if !isInputParameter(k, li)
        push!(locals, k)
    end
  end
  for i in 1:length(li.gen_sym_typs)
      push!(locals, GenSym(i-1))
  end
  return locals
end

end

"""
Returns an array of Symbols for escaping variables. 
"""
function getEscapingVariables(li :: LambdaVarInfo)
  return keys(li.escaping_defs)
end

"""
Returns true if the Symbol in "s" is an escaping variable in LambdaVarInfo in "li".
"""
function isEscapingVariable(s :: Symbol, li :: LambdaVarInfo)
  return haskey(li.escaping_defs, s) && !isInputParameter(s, li)
end

"""
Returns true if the GenSym in "s" is a GenSym in LambdaVarInfo in "li".
"""
function isLocalGenSym(s :: GenSym, li :: LambdaVarInfo)
  return s.id >= 0 && s.id < size(li.gen_sym_typs, 1)
end

"""
Add multiple local variables from some collection type.
"""
function addLocalVariables(collection, li :: LambdaVarInfo)
  for i in collection
    addLocalVariable(i, li)
  end
end

"""
Adds a local variable from a VarDef to the given LambdaVarInfo.
"""
function addLocalVariable(vd :: VarDef, li :: LambdaVarInfo)
  addLocalVariable(vd.name, vd.typ, vd.desc, li)
end

"""
Add one or more bitfields in "desc_flag" to the descriptor for a variable.
"""
function addDescFlag(s :: Symbol, desc_flag, li :: LambdaVarInfo)
  if haskey(li.var_defs, s)
    var_def      = li.var_defs[s]
    var_def.desc = var_def.desc | desc_flag
    return true
  else
    return false
  end
end

"""
Adds a new local variable with the given Symbol "s", type "typ", descriptor "desc" in LambdaVarInfo "li".
Returns true if the variable already existed and its type and descriptor were updated, false otherwise.
"""
@noinline function addLocalVariable(s :: Symbol, typ, desc, li :: LambdaVarInfo)
  # If it is already a local variable then just update its type and desc.
  if haskey(li.var_defs, s)
    var_def      = li.var_defs[s]
    @dprintln(3,"addLocalVariable ", s, " already exists with type ", var_def.typ)
    var_def.typ  = typ
    var_def.desc = desc
    return true
  end

if VERSION > v"0.5.0-dev+3260"
  li.var_defs[s] = VarDef(s, typ, desc, length(li.var_defs) + 1)
else
  li.var_defs[s] = VarDef(s, typ, desc)
end
  @dprintln(3,"addLocalVariable = ", s)

  return false
end

"""
Adds a new escaping variable with the given Symbol "s", type "typ", descriptor "desc" in LambdaVarInfo "li".
Returns true if the variable already existed and its type and descriptor were updated, false otherwise.
"""
function addEscapingVariable(s :: Symbol, typ, desc, li :: LambdaVarInfo)
  assert(!isInputParameter(s, li))
  # If it is already a local variable then just update its type and desc.
  if haskey(li.escaping_defs, s)
    var_def      = li.var_defs[s]
    @dprintln(3,"addEscapingVariable ", s, " already exists with type ", var_def.typ)
    var_def.typ  = typ
    var_def.desc = desc
    return true
  end

if VERSION > v"0.5.0-dev+3260"
  # FIX FIX FIX the -1 here.
  li.escaping_defs[s] = VarDef(s, typ, desc, -1)
else
  li.escaping_defs[s] = VarDef(s, typ, desc)
end
  @dprintln(3,"addEscapingVariable = ", s)

  return false
end

"""
Adds a new escaping variable from a VarDef in parameter "vd" into LambdaVarInfo "li".
"""
function addEscapingVariable(vd :: VarDef, li :: LambdaVarInfo)
  addEscapingVariable(vd.name, vd.typ, vd.desc, li)
end

"""
Deletes a new escaping variable from a VarDef in parameter "vd" into LambdaVarInfo "li".
"""
function deleteEscapingVariable(s :: Symbol, li :: LambdaVarInfo)
  delete!(li.escaping_defs, s)
end

"""
Add a new GenSym to the LambdaVarInfo in "li" with the given type in "typ".
Returns the new GenSym.
"""
function addGenSym(typ, li :: LambdaVarInfo)
  push!(li.gen_sym_typs, typ)
  return GenSym(length(li.gen_sym_typs) - 1) 
end

"""
Add a local variable to the function corresponding to LambdaVarInfo in "li" with name (as String), type and descriptor.
Returns true if variable already existed and was updated, false otherwise.
"""
function addLocalVar(name :: AbstractString, typ, desc, li :: LambdaVarInfo)
  addLocalVar(Symbol(name), typ, desc, li)
end

"""
Add a local variable to the function corresponding to LambdaVarInfo in "li" with name (as Symbol), type and descriptor.
Returns true if variable already existed and was updated, false otherwise.
"""
function addLocalVar(name :: Symbol, typ, desc, li :: LambdaVarInfo)
  addLocalVariable(name, typ, desc, li)
end

"""
Remove a local variable from lambda "li" given the variable's "name".
Returns true if the variable existed and it was removed, false otherwise.
"""
function removeLocalVar(name :: Symbol, li :: LambdaVarInfo)
  if haskey(li.var_defs, name)
    delete!(li.var_defs, name)
    return true
  else
    return false
  end
end

if VERSION > v"0.5.0-dev+3260"
"""
Convert the lambda expression's args[2][1] from Array{Array{Any,1},1} to a Dict{Symbol,VarDef}.
The internal triples are extracted and asserted that name and desc are of the appropriate type.
"""
function createVarDict(x :: LambdaInfo)
  ret = Dict{Symbol,VarDef}()
  @dprintln(1,"createVarDict ", x)
  numslots = length(x.slotnames)
  assert(numslots == length(x.slottypes))
  assert(numslots == length(x.slotflags))
  for i = 1:numslots
    name = x.slotnames[i]
    typ  = x.slottypes[i]
    desc = x.slotflags[i]
    @dprintln(2,"name = ", name, " typ = ", typ, " flags = ", desc)
    if typeof(name) != Symbol
      @dprintln(0, "name is not of type symbol ", name, " type = ", typeof(name))
    end
    if typeof(desc) != UInt8
      @dprintln(0, "desc is not of type Int64 ", desc, " type = ", typeof(desc))
    end
    if typeof(typ) == DataType
        ret[name] = VarDef(name, typ, desc, i)
    else
      @dprintln(1, "typ is not a DataType ", typ, " type = ", typeof(typ))
    end
  end
  return ret
end
else
"""
Convert the lambda expression's args[2][1] from Array{Array{Any,1},1} to a Dict{Symbol,VarDef}.
The internal triples are extracted and asserted that name and desc are of the appropriate type.
"""
function createVarDict(x :: Array{Any, 1})
  ret = Dict{Symbol,VarDef}()
  @dprintln(1,"createVarDict ", x)
  for i = 1:length(x)
    @dprintln(1,"x[i] = ", x[i])
    name = x[i][1]
    typ  = x[i][2]
    desc = x[i][3]
    if typeof(name) != Symbol
      @dprintln(0, "name is not of type symbol ", name, " type = ", typeof(name))
    end
    if typeof(desc) != Int64
      @dprintln(0, "desc is not of type Int64 ", desc, " type = ", typeof(desc))
    end
    if typeof(typ) == DataType
        ret[name] = VarDef(name, typ, desc)
    else
      @dprintln(1, "typ is not a DataType ", typ, " type = ", typeof(typ))
    end
  end
  return ret
end
end

"""
Replace the symbols in an expression "expr" with those defined in the
dictionary "dict".  Return the result expression, which may share part of the
input expression, but the input "expr" remains intact and is not modified.

Note that unlike "replaceExprWithDict!", we do not recurse down nested lambda
expressions (i.e., LambdaStaticData or DomainLambda or any other none Expr
objects are left unchanged). If such lambdas have escaping names that are to be
replaced, then the result will be wrong.
"""
function replaceExprWithDict(expr::Any, dict::Dict{LHSVar, Any})
  function traverse(expr :: ANY)       # traverse expr to find the places where arrSym is refernced
    if isa(expr, Symbol) || isa(expr, GenSym)
      if haskey(dict, expr)
        return dict[expr]
      end
      return expr
    elseif isa(expr, TypedVar)
      lhsVar = toLHSVar(expr)
      if haskey(dict, lhsVar)
        return dict[lhsVar]
      end
      return expr
    elseif isa(expr, Array)
      Any[ traverse(e) for e in expr ]
    elseif isa(expr, Expr)
      local head = expr.head
      local args = copy(expr.args)
      local typ  = expr.typ
      for i = 1:length(args)
        args[i] = traverse(args[i])
      end
      expr = Expr(expr.head, args...)
      expr.typ = typ
      return expr
    else
      expr
    end
  end
  expr=traverse(expr)
  return expr
end


"""
Replace the symbols in an expression "expr" with those defined in the
dictionary "dict".  Return the result expression, which may share part of the
input expression, and the input "expr" may be modified inplace and shall not be used
after this call. Note that unlike "replaceExprWithDict", the traversal here is
done by ASTWalker, which has the ability to traverse non-Expr data.
"""
function replaceExprWithDict!(expr :: ANY, dict :: Dict{LHSVar, Any}, AstWalkFunc = nothing)
  function update_sym(expr :: ANY, dict, top_level_number :: Int64, is_top_level :: Bool, read :: Bool)
    if isa(expr, Symbol) || isa(expr, GenSym)
      if haskey(dict, expr)
        return dict[expr]
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
  @dprintln(3,"outer = ", outer)
  @dprintln(3,"inner = ", inner)
  for (v, d) in inner.var_defs
    if isLocalVariable(v, outer) 
      if !isInputParameter(v, inner) # skip input parameters
        error("Conflicting variable ", v, " exists in both inner and outer lambda")
      end
    else
      addLocalVariable(d, outer)
    end
  end
  outer.var_defs = merge(outer.var_defs, inner.var_defs)
  for (v, d) in inner.escaping_defs
    if !isLocalVariable(v, outer) && !isInputParameter(v, outer) && !isEscapingVariable(v, outer)
      @dprintln(1, string("Variable ", v, " from inner lambda is neither parameter nor local nor escaping in outer lambda"))
    end
  end
  n = length(outer.gen_sym_typs)
  dict = Dict{LHSVar, Any}()
  for i = 1:length(inner.gen_sym_typs)
    push!(outer.gen_sym_typs, inner.gen_sym_typs[i])
    old_sym = GenSym(i - 1)
    new_sym = GenSym(n + i - 1)
    dict[old_sym] = new_sym
  end
  return dict
end

if VERSION > v"0.5.0-dev+3260"

function lambdaToLambdaVarInfo(lambda :: LambdaInfo)
  ret = LambdaVarInfo(lambda)
  for i = 2:lambda.nargs
    one_input = lambda.slotnames[i]
    push!(ret.input_params, one_input)
    # the following is commented out because we need to handle varargs
    #oityp = typeof(one_input)
    #if oityp == Symbol
    #  push!(ret.input_params, one_input)
    #elseif oityp == Expr && one_input.head == :(::)
    #  push!(ret.input_params, one_input.args[1])
    #else
    #  @dprintln(0, "Converting lambda expresison to lambda info found unhandled input parameter type.  input = ", one_input, " type = ", oityp)
    #end
  end

  # Create a searchable dictionary mapping symbols to their VarDef information.
  ret.var_defs = createVarDict(lambda)
# FIX FIX FIX
#  ret.escaping_defs = createVarDict(meta[2])
  ssafieldname = VERSION >= v"0.5.0-dev+3875" ? :ssavaluetypes : :gensymtypes
  if !isa(getfield(lambda, ssafieldname), Array) 
    ret.gen_sym_typs = Any[]
  else
    ret.gen_sym_typs = getfield(lambda, ssafieldname)
  end
#  ret.static_parameter_names = length(meta) > 3 ? meta[4] : Any[]

  ret.return_type = lambda.rettype

  @dprintln(3,"Result of lambdaToLambdaVarInfo = ", ret)
  return ret
end

else
"""
Convert a lambda expression into our internal storage format, LambdaVarInfo.
The input is asserted to be an expression whose head is :lambda.
"""
function lambdaToLambdaVarInfo(lambda :: LambdaStaticData)
  lambdaToLambdaVarInfo(Base.uncompressed_ast(lambda))
end

function lambdaToLambdaVarInfo(lambda :: Expr)
  assert(lambda.head == :lambda)
  assert(length(lambda.args) == 3)

  ret = LambdaVarInfo(lambda)
  for i = 1:length(lambda.args[1])
    one_input = lambda.args[1][i]
    push!(ret.input_params, one_input)
    # the following is commented out because we need to handle varargs
    #oityp = typeof(one_input)
    #if oityp == Symbol
    #  push!(ret.input_params, one_input)
    #elseif oityp == Expr && one_input.head == :(::)
    #  push!(ret.input_params, one_input.args[1])
    #else
    #  @dprintln(0, "Converting lambda expresison to lambda info found unhandled input parameter type.  input = ", one_input, " type = ", oityp)
    #end
  end

  # We call the second part of the lambda metadata.
  meta = lambda.args[2]
  @dprintln(1,"meta = ", meta)
  # Create a searchable dictionary mapping symbols to their VarDef information.
  ret.var_defs = createVarDict(meta[1])
  ret.escaping_defs = createVarDict(meta[2])
  if !isa(meta[3], Array) 
    ret.gen_sym_typs = Any[]
  else
    ret.gen_sym_typs = meta[3]
  end
  ret.static_parameter_names = length(meta) > 3 ? meta[4] : Any[]

  assert(typeof(lambda.args[3]) == Expr)
  assert(lambda.args[3].head == :body)
  ret.return_type = lambda.args[3].typ

  return ret
end
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
    throw(string("Force inference LambdaInfo not supported yet in lambdaTypeinf"))
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
    meth = Base._methods(ftyp, typs, -1)
    if length(meth) == 1
#        println("meth in _methods ", meth)
        meth = meth[1]
        linfo = Base.func_for_method_checked(meth[3], typs)
        (tree, ty) = Core.Inference.typeinf_uncached(linfo, meth[1], meth[2], optimize = optimize)
#        println("lambdaTypeinf typeof(tree) = ", typeof(tree), " typeof(ty) = ", typeof(ty))
        return tree, ty
    else
        throw(string("Expected one method from call to Base._methods in lambdaTypeinf."))
    end
else
    lambda = Core.Inference.func_for_method(ftyp.name.mt.defs, typs, env)
#    println("lambdaTypeinf typeof(lambda) = ", typeof(lambda))
    (tree, ty) = Core.Inference.typeinf_uncached(lambda, types, Core.svec(), optimize = optimize)
#    println("lambdaTypeinf typeof(tree) = ", typeof(tree), " typeof(ty) = ", typeof(ty))
    lambda.ast = tree
    return lambda, ty
end
end

"""
Convert the Dict{Symbol,VarDef} internal storage format from a dictionary back into an array of Any triples.
"""
function dictToArray(x :: Dict{Symbol,VarDef})
  ret = Any[]
  for (k, s) in x
    push!(ret, [s.name; s.typ; s.desc])
  end
  return ret
end

"""
Create the args[2] part of a lambda expression given an object of our internal storage format LambdaVarInfo.
"""
function createMeta(LambdaVarInfo :: LambdaVarInfo)
  ret = Any[]

  push!(ret, dictToArray(LambdaVarInfo.var_defs))
  push!(ret, dictToArray(LambdaVarInfo.escaping_defs))
  push!(ret, LambdaVarInfo.gen_sym_typs)
  push!(ret, LambdaVarInfo.static_parameter_names)

  return ret
end

if VERSION > v"0.5.0-dev+3260"
function LambdaVarInfoToLambda(LambdaVarInfo :: LambdaVarInfo, body::Array{Any,1})
  li = LambdaVarInfo.orig_info
  li.code =  ccall(:jl_compress_ast, Any, (Any,Any), li, body)
  return li
end
else
"""
Convert our internal storage format, LambdaVarInfo, back into a lambda expression.
This takes a LambdaVarInfo and a body as input parameters.
This body can be a body expression or you can pass "nothing" if you want but then you will probably need to set the body in args[3] manually by yourself.
"""
function LambdaVarInfoToLambda(LambdaVarInfo :: LambdaVarInfo, body::Array{Any,1})
  expr = Expr(:body)
  expr.args = body
  if LambdaVarInfo.return_type != nothing
      expr.typ = LambdaVarInfo.return_type
  end
  return Expr(:lambda, LambdaVarInfo.input_params, createMeta(LambdaVarInfo), expr)
end
end

function LambdaVarInfoToLambda(LambdaVarInfo :: LambdaVarInfo, body_expr :: Expr)
  assert(body_expr.head == :body)
  LambdaVarInfoToLambda(LambdaVarInfo, body_expr.args)
end

"""
Update the descriptor part of the VarDef dealing with whether the variable is assigned or not in the function.
Takes the LambdaVarInfo and a dictionary that maps symbols names to the number of times they are statically assigned in the function.
"""
function updateAssignedDesc(LambdaVarInfo :: LambdaVarInfo, symbol_assigns :: Dict{Symbol,Int})
  # For each VarDef
  for i in LambdaVarInfo.var_defs
    # If that VarDef's symbol is in the dictionary.
    if haskey(symbol_assigns, i[1])
      var_def = i[2]
      # Get how many times the symbol is assigned to.
      num_assigns = symbol_assigns[var_def.name]
      # Remove the parts of the descriptor dealing with the number of assignments.
      var_def.desc = var_def.desc & (~ (ISASSIGNED | ISASSIGNEDONCE)) 
      if num_assigns > 1
        # If more than one assignment then OR on ISASSIGNED.
        var_def.desc = var_def.desc | ISASSIGNED
      elseif num_assigns == 1
        # If exactly one assignment then OR on ISASSIGNED and ISASSIGNEDONCE
        var_def.desc = var_def.desc | ISASSIGNED | ISASSIGNEDONCE
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

function getBody(lambda :: LambdaVarInfo)
  return getBody(lambda.orig_info)
end

function getBody(lambda :: Expr)
  assert(lambda.head == :lambda)
  return lambda.args[3]
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
function getRefParams(LambdaVarInfo :: LambdaVarInfo)
  ret = Symbol[]

  input_vars = LambdaVarInfo.input_params
  var_types  = LambdaVarInfo.var_defs

  @dprintln(3,"input_vars = ", input_vars)
  @dprintln(3,"var_types = ", var_types)

  for iv in input_vars
    @dprintln(3,"iv = ", iv, " type = ", typeof(iv))
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

"""
Convert a parameter to Symbol.
"""
parameterToSymbol(x, info::LambdaVarInfo) = getVariableName(x, info)

"""
Get the name of a local variable, either as Symbol or GenSym
"""
getVariableName(x::GenSym, info::LambdaVarInfo) = x
getVariableName(x::Symbol, info::LambdaVarInfo) = x
genWithRename(x::Symbol, new_name::Symbol, linfo::LambdaVarInfo) = new_name
if VERSION > v"0.5.0-dev+3260"
getVariableName(x::TypedSlot,  info::LambdaVarInfo) = info.orig_info.slotnames[x.id]
getVariableName(x::SlotNumber, info::LambdaVarInfo) = info.orig_info.slotnames[x.id]
updateType(li::LambdaVarInfo, x::SlotNumber, typ) = updateType(li, getVariableName(x, li), typ)
getDesc(x :: SlotNumber, li :: LambdaVarInfo) = getDesc(getVariableName(x, li), li)
genWithRename(x::TypedSlot,  new_name::Symbol, linfo::LambdaVarInfo) = TypedSlot(symbolToSlotId(new_name, linfo), x.typ)
genWithRename(x::SlotNumber, new_name::Symbol, linfo::LambdaVarInfo) = SlotNumber(symbolToSlotId(new_name, linfo))
else
getVariableName(x::SymbolNode, info::LambdaVarInfo) = x.name
genWithRename(x::SymbolNode, new_name::Symbol, linfo::LambdaVarInfo) = SymbolNode(new_name, x.typ)
end
getVariableName(x::Expr, info::LambdaVarInfo) = begin assert(x.head == :(::)); return x.args[1] end
genWithRename(x::Expr, new_name::Symbol, info::LambdaVarInfo) = begin assert(x.head == :(::)); return TypedExpr(x.typ, :(::), new_name, x.args[2]) end

end
