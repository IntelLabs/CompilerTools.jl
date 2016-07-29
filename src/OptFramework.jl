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

module OptFramework

import ..DebugMsg
DebugMsg.init()

using CompilerTools
using CompilerTools.Helper

export @acc, @noacc, addOptPass
export PASS_MACRO, PASS_LOWERED, PASS_UNOPTTYPED, PASS_TYPED


const PASS_MACRO = 0 :: Int
const PASS_LOWERED = 1 :: Int
const PASS_UNOPTTYPED = 2 :: Int
const PASS_TYPED = 3 :: Int

"""
pretty print pass level number as string.
"""
function dumpLevel(level)
  if level == PASS_MACRO "macro AST"
  elseif level == PASS_LOWERED "lowered AST"
  elseif level == PASS_UNOPTTYPED "unoptimized typed AST"
  elseif level == PASS_TYPED "typed AST"
  else "unknown AST"
  end
end

"""
A data structure that holds information about one high-level optimization pass to run.
"func" is the callback function that does the optimization pass and should have the signature (GlobalRef, Expr, Tuple) where the GlobalRef provides the locate of the function to be optimized, Expr is the AST input to this pass, and Tuple is a tuple of all parameter types of the functions. It must return either an optimized Expr, or a Function.
"level" indicates at which level this pass is to be run. 
"""
type OptPass
    func  :: Function
    level :: Int # at which level this OptPass is run
end

# Stores the default set of optimization passes if they are not specified on a line-by-line basis.
optPasses = OptPass[]

"""
Set the default set of optimization passes to apply with the @acc macro. 
"""
function setOptPasses(passes :: Array{OptPass,1})
  for pass in passes
    addOptPass(pass)
  end
end

"""
Sometimes the original function shouldn't be evaluated since it is not valid Julia syntax.
This happens when DSL constructs are used that cannot have function implementations.
    motivation: DataTables in HPAT
"""
saveOriginalFunction = true
function setSaveOriginalFunction(val::Bool)
    global saveOriginalFunction = val
end

"""
Add an optimization pass. If this is going to be called multiple times then you need some external way of corrdinating the code/modules that are calling this function so that optimization passes are added in some sane order.
"""
function addOptPass(pass :: OptPass)
  level = -1
  if length(optPasses) > 0
    level = optPasses[end].level
  end
  if pass.level < level
      throw(string("Optimization passes cannot handle ", dumpLevel(pass.level), " pass after ", dumpLevel(level)))
  end
  @dprintln(2, "Add optimization pass at level ", dumpLevel(pass.level))
  push!(optPasses, pass) 
end

"""
Same as the other addOptPass but with a pass call back function and pass level as input.
"""
function addOptPass(func, level)
  addOptPass(OptPass(func, level))
end

"""
Retrieve the AST of the given function "func" and signature "sig" for at the given pass "level".
"""
function getCodeAtLevel(func, sig::Tuple, level)
  if level == PASS_MACRO 
    error("AST at macro level must be passed in, and cannot be obtained from inspecting the function itself")
  elseif level == PASS_LOWERED 
    ast = code_lowered(func, sig)
  elseif level == PASS_UNOPTTYPED 
    ast = code_typed(func, sig, optimize=false)
  elseif level == PASS_TYPED
    ast = code_typed(func, sig, optimize=true)
  else 
    error("Unknown AST level: ", level)
  end
  @dprintln(3, "getCodeAtLevel ", dumpLevel(level), " ast = ", ast)
  @assert (length(ast) > 0) ("Failed to retrieve AST for function " * dump(func) * " with signature " * dump(sig))
  @assert (length(ast) == 1) ("Expect one AST but got many for function " * dump(func) * " with signature " * dump(sig) * ": " * dump(ast))
  @dprintln(3, "typeof(ast[1]) ", typeof(ast[1]))
  @assert (isfunctionhead(ast[1])) ("Expected function head but got " * dump(ast[1]))
  @dprintln(3, "getCodeAtLevel returns")
  return ast[1]
end

"""
convert AST from "old_level" to "new_level". The input "ast" can be either Expr or Function type. In the latter case, the result AST will be obtained from this function using an matching signature "sig". The last "func" is a skeleton function that is used internally to facility such conversion.
"""
function convertCodeToLevel(ast :: ANY, sig :: ANY, old_level, new_level, func)
  @dprintln(3,"convertCodeToLevel sig = ", sig, " ", old_level, "=>", new_level, " func = ", func, " typeof(sig) = ", typeof(sig), " typeof(ast) = ", typeof(ast), " typeof(func) = ", typeof(func))
  if isa(ast, Function)
    return getCodeAtLevel(ast, sig, new_level)
  end
  if old_level == new_level
    return ast
  end
  if old_level == PASS_MACRO
    error("Code in macro must be evaled first before converted")
  else
    func_methods = methods(func, sig)
    @assert (length(func_methods) == 1) ("Expect only one matching method for " * func * " of signature " * sig * " but got " * length(func_methods))
    lambda = func_methods[1].func.code
    @assert (isa(lambda, LambdaInfo)) ("LambdaInfo not found for " * func * " of signature " * sig)
    lambda.ast = ccall(:jl_compress_ast, Any, (Any,Any), lambda, ast)
    if new_level == PASS_UNOPTTYPED
      @dprintln(3,"Calling lambdaTypeinf with optimize=false")
      (new_ast, rty) = CompilerTools.LambdaHandling.lambdaTypeinf(lambda, sig, optimize=false)
    else
      assert(new_level == PASS_TYPED)
      @dprintln(3,"Calling lambdaTypeinf with optimize=true")
      @dprintln(4,"lambda = ", lambda)
      new_ast = ast
      #(new_ast, rty) = CompilerTools.LambdaHandling.lambdaTypeinf(lambda, sig, optimize=true)
    end
    @assert (isa(new_ast, Expr) && new_ast.head == :lambda) ("Expect Expr with :lambda head, but got " * new_ast)
    return new_ast
  end 
end

"""
A global memo-table that maps both: the triple (function, signature, optPasses) to the trampoline function, and the trampoline function to the real function.
"""
gOptFrameworkDict = Dict{Any,Any}()

"""
This function removes duplicate labels.
"""
function removeDupLabels(stmts)
  if length(stmts) == 0
    return Any[]
  end

  ret = Any[]

  push!(ret, stmts[1])
  last_is_label = false
  last_label = -1
  labelMap = Dict{Int,Int}()
  
  for i = 2:length(stmts)
    if isa(stmts[i], LabelNode)
      if last_is_label
         labelMap[stmts[i].label] = last_label
         continue
      else
         last_is_label = true
         last_label = stmts[i].label
         labelMap[last_label] = last_label
      end
    elseif isa(stmts[i], LineNumberNode)
    else
      last_is_label = false
    end
    push!(ret, stmts[i])
    #push!(ret, LineNumberNode(i))
  end

  updateBodyWithLabelMap!(ret, labelMap)

  ret
end

function updateBodyWithLabelMap!(body::Array{Any,1}, labelMap :: Dict{Int,Int})
  for i=1:length(body)
    if isa(body[i], LabelNode)
      body[i] = LabelNode(labelMap[body[i].label])
    elseif isa(body[i], GotoNode) 
      body[i] = GotoNode(labelMap[body[i].label])
    elseif isa(body[i], Expr) && (body[i].head === :gotoifnot)
      body[i].args[2] = labelMap[body[i].args[2]]
    end
  end
end

"""
Update labels with a new base, return the max label.
"""
function updateLabels!(body::Array{Any,1}, base=0)
  labelMap = Dict{Int,Int}()
  for i=1:length(body)
    if isa(body[i], LabelNode) 
      labelMap[body[i].label] = base + i
    end
  end
  updateBodyWithLabelMap!(body, labelMap)
  return base + length(body)
end

"""
Clean up the labels in AST by renaming them, and removing duplicates.
"""
function cleanupBodyLabels(expr::Expr)
  @assert (expr.head == :body)
  @dprintln(3, "cleanupBodyLabels ", expr)
  body = removeDupLabels(expr.args)
  expr.args = body
  @dprintln(3, "cleanupBodyLabels after remove dup labels ", expr)
  max_label = updateLabels!(body)
  expr.args = body
  @dprintln(3, "cleanupBodyLabels after updateLabels! ", expr)
  expr.args = body
  return expr
end

function cleanupBodyLabels(body::Array)
  expr = Expr(:body)
  expr.args = body
  return cleanupBodyLabels(expr).args
end

function eliminateParamAssigns(linfo, body)
  @dprintln(3,"eliminateParamAssigns: body = ", body)
  # Create a set of the input parameters in LHSVar form.
  input_lhsvars = Set{LHSVar}(CompilerTools.LambdaHandling.getInputParametersAsLHSVar(linfo))
  @dprintln(3,"eliminateParamAssigns: input_lhsvars = ", input_lhsvars)
  # Do liveness analysis on the body.
  lives = CompilerTools.LivenessAnalysis.from_lambda(linfo, body)
  assigned_params = Set{LHSVar}()
  # For each basic block in the AST.
  for bbentry in lives.basic_blocks
    bb = bbentry[2]
    # Find which input parameters are assigned in the block by the intersection of the input lhsvars and the definitions in the basic block.
    # Add those modified parameters to the set of all modified parameters in assigned_params.
    assigned_params = union(assigned_params, intersect(input_lhsvars, bb.def))
    @dprintln(3,"eliminateParamAssigns: assigned_params = ", assigned_params, " bb.def = ", bb.def)
  end  

  new_body = Any[]

  rdict = Dict{LHSVar, Any}()
  for ap in assigned_params
    vd = CompilerTools.LambdaHandling.getVarDef(ap, linfo)
    @dprintln(3,"eliminateParamAssigns: vd = ", vd)
    rhsvar_copy = CompilerTools.LambdaHandling.addLocalVariable(Symbol(string(vd.name, "_duplicate_to_eliminate_param_assign")), vd.typ, CompilerTools.LambdaHandling.ISASSIGNED, linfo)
    rdict[ap] = rhsvar_copy 
    push!(new_body, TypedExpr(vd.typ, :(=), toLHSVar(rhsvar_copy), ap))
  end
  @dprintln(3,"new_body = ", new_body)

  if !isempty(rdict)
      body = CompilerTools.LambdaHandling.replaceExprWithDict!(body, rdict)
      @dprintln(3,"body after replaceExprWithDict! = ", body, " type = ", typeof(body))
#      for i = 1:3
#          push!(new_body, body.args[i])
#      end
#      push!(new_body, Expr(:return, 1.0))
      append!(new_body, body.args)
      body.args = new_body
      @dprintln(3,"eliminateParamAssigns: final body = ", body)
      @dprintln(3,"eliminateParamAssigns: linfo = ", linfo)
  end

  return linfo, body
end

function cleanupFunction(linfo, body)
  linfo, new_body = eliminateParamAssigns(linfo, body)
  @dprintln(3, "new_body = ", new_body, " type = ", typeof(new_body))
  new_body = CompilerTools.AstWalker.AstWalk(new_body, invoke_to_call, nothing)
  @dprintln(3, "new_body after transforming invoke back to call = ", new_body)
  new_body = cleanupBodyLabels(new_body)
  @dprintln(3, "new_body after label cleanup = ", new_body)
  #new_body_args = CompilerTools.LambdaHandling.getBody(ast).args
  return linfo, new_body
end

if VERSION > v"0.5.0-dev+3260"
"""
Makes sure that a newly created function is correctly present in the internal Julia method table.
"""
function setCode(func, arg_tuple, ast)
  assert(isfunctionhead(ast))
  #tfuncPresent(func, arg_tuple)
  @dprintln(2, "setCode fields of ast")
#  CompilerTools.Helper.print_by_field(ast)
  @dprintln(2, "setCode fields of ast.def")
#  CompilerTools.Helper.print_by_field(ast.def)

  info = code_typed(func, arg_tuple)[1]
  meth_list = methods(func, arg_tuple).ms
  @dprintln(2, "meth_list = ", meth_list, " type = ", typeof(meth_list), " len = ", length(meth_list))
  def = meth_list[1]
  assert(isa(def,Method))

  @dprintln(2, "ast slotnames: ", ast.slotnames)
#  @dprintln(2, "setCode fields of def")
#  CompilerTools.Helper.print_by_field(def)
  @dprintln(2, "typeof(def.specializations) = ", typeof(def.specializations))
#  @dprintln(2, "setCode fields of def.specializations")
#  CompilerTools.Helper.print_by_field(def.specializations)
  #assert(isa(def.specializations.func, LambdaInfo))
#  @dprintln(2, "setCode fields of def.specializations.func")
#  CompilerTools.Helper.print_by_field(def.tfunc.func)

  #ast.code = deepcopy(CompilerTools.LambdaHandling.getBody(ast).args)
  def.specializations = nothing
  #def.specializations.func = ast
  #def.specializations.func.def = def
#  ast.code = new_body.args # ccall(:jl_compress_ast, Any, (Any,Any), ast, new_body_args)
  def.lambda_template = ast # def.specializations.func
  ast.slotnames[1] = info.slotnames[1]
  ast.slottypes[1] = info.slottypes[1]
  ast.slotflags[1] = info.slotflags[1]
  @dprintln(2, ast)

  #throw(string("stop here"))
  #ast.inferred = true
  #@dprintln(2, printExprAst(ast))
  precompile(func, arg_tuple)
  @dprintln(2, "setCode fields of def after")
#  CompilerTools.Helper.print_by_field(def)
  @dprintln(2, "setCode fields of def.specializations.func after")
#  CompilerTools.Helper.print_by_field(def.tfunc.func)

  #@dprintln(2, def.specializations)
  @dprintln(2, "code typed")
  @dprintln(2, code_typed(func, arg_tuple))
  @dprintln(2, "Done precompiling.")
end

else
"""
Makes sure that a newly created function is correctly present in the internal Julia method table.
"""
function tfuncPresent(func, tt)
  meth_list = methods(func, tt)
  @dprintln(2, "meth_list = ", meth_list, " type = ", typeof(meth_list))
  m = meth_list[1]
  def = m.func.code
  if is(def.tfunc, nothing)
    @dprintln(2, "tfunc NOT present before code_typed")
    code_typed(func, tt)
    if is(def.tfunc, nothing) 
      error("tfunc still NOT present after code_typed")
    else
      @dprintln(2, "tfunc present after code_typed")
    end
  else
    @dprintln(2, "tfunc present on call")
  end 
end

function setCode(func, arg_tuple, ast)  
  assert(isfunctionhead(ast))  
  tfuncPresent(func, arg_tuple)
  method = methods(new_func, call_sig_arg_tuple)
  assert(length(method) == 1) 
  method = method[1]      
  @dprintln(2, "tfunc type = ", typeof(method.func.code.tfunc))
  method.func.code.tfunc[2] = ccall(:jl_compress_ast, Any, (Any,Any), method.func.code, ast)
end
end

"""
Takes a function, a signature, and a set of optimizations and applies that set of optimizations to the function,
returns a new optimized function without modifying the input.  Argument explanation follows:
1) func - the function being optimized
2) call_sig_arg_tuple - the signature of the function, i.e., the types of each of its arguments
3) per_site_opt_set - the set of optimization passes to apply to this function.
"""
function processFuncCall(func :: ANY, call_sig_arg_tuple :: ANY, per_site_opt_set :: ANY)
  @dprintln(3,"processFuncCall starting = ", func, " func type = ", typeof(func), " call_sig_arg_tuple = ", call_sig_arg_tuple)
  @assert (isa(func, Function)) ("processFuncCall can only optimize functions, but got " * typeof(func))
  if per_site_opt_set == nothing 
    per_site_opt_set = optPasses 
  end
  @assert (length(per_site_opt_set) > 0) "There are no registered optimization passes."
  func_module = Base.function_module(func, call_sig_arg_tuple)
  func_ref = GlobalRef(func_module, Base.function_name(func))
  @dprintln(3,"processFuncCall ", func_ref, " ", call_sig_arg_tuple, " opt_set = ", per_site_opt_set)

  # Create a skeleton of the incoming function, which is used to facilitate AST conversion, and will eventually be the result function to be returned.
  new_func_name = gensym(string(func_ref))
  fake_args = Any[ gensym() for a in call_sig_arg_tuple ]
  new_func = Core.eval(func_module, :(function $(new_func_name)($(fake_args...)) end))
  @dprintln(2,"temp_func is ", new_func)
  code_typed(new_func, call_sig_arg_tuple)

  # Remember what level the AST was in.
  cur_level = per_site_opt_set[1].level
  cur_ast = func

  @dprintln(3,"Initial code to optimize = ", cur_ast)

  # For each optimization pass in the optimization set.
  for i = 1:length(per_site_opt_set)
      @dprintln(3,"optimization pass ", i)
      # See if the current optimization pass uses optimized AST form and the previous optimization pass used unoptimized AST form.
      cur_level = per_site_opt_set[i].level
      if cur_level > PASS_MACRO
        cur_ast = convertCodeToLevel(cur_ast, call_sig_arg_tuple, cur_level, cur_level, new_func)
        #assert(isfunctionhead(cur_ast))
        # Call the current optimization on the current AST.
        try
          cur_ast = per_site_opt_set[i].func(func_ref, cur_ast, call_sig_arg_tuple)
          #assert(isfunctionhead(cur_ast) || isa(cur_ast, Function))
        catch texp
          if CompilerTools.DebugMsg.PROSPECT_DEV_MODE
            rethrow(texp)
          end
          println("OptFramework failed to optimize function ", func, " in optimization pass ", per_site_opt_set[i].func, " with error ", texp)
          return nothing
        end
        @dprintln(3,"AST after optimization pass ", i, " = ", cur_ast)
      end
  end

  @dprintln(3,"After optimization passes")

  #if isa(cur_ast, Expr)
  if isa(cur_ast,Tuple) && length(cur_ast)==2 && isa(cur_ast[1], CompilerTools.LambdaHandling.LambdaVarInfo) && isa(cur_ast[2], Expr)
    lvi = cur_ast[1]
    body = cur_ast[2]
    @dprintln(3,"After last optimization pass, got Tuple of LambdaVarInfo and Expr with head = ", body.head)
    linfo, body = convertCodeToLevel(cur_ast, call_sig_arg_tuple, cur_level, PASS_TYPED, new_func)
    linfo, body = cleanupFunction(linfo, body)
    ast = CompilerTools.LambdaHandling.LambdaVarInfoToLambda(linfo, body)
    assert(isfunctionhead(ast))
    @dprintln(3,"Last opt pass after converting to typed AST.\n", CompilerTools.LambdaHandling.getBody(ast))
    setCode(new_func, call_sig_arg_tuple, ast)

    @dprintln(3,"Final processFuncCall = ", code_typed(new_func, call_sig_arg_tuple)[1])
    return new_func
  elseif isfunctionhead(cur_ast)
    ast = convertCodeToLevel(cur_ast, call_sig_arg_tuple, cur_level, PASS_TYPED, new_func)
    assert(isfunctionhead(ast))
    @dprintln(3,"Last opt pass after converting to typed AST.\n", CompilerTools.LambdaHandling.getBody(ast))

    # Write the modifed code back to the function.
    @dprintln(2,"Before methods at end of processFuncCall.")
    setCode(new_func, call_sig_arg_tuple, ast)
#    tfuncPresent(new_func, call_sig_arg_tuple)
#    method = methods(new_func, call_sig_arg_tuple)
#    assert(length(method) == 1)
#    method = method[1]
#    method.func.code.tfunc[2] = ccall(:jl_compress_ast, Any, (Any,Any), method.func.code, cur_ast)

    @dprintln(3,"Final processFuncCall = ", code_typed(new_func, call_sig_arg_tuple)[1])
    return new_func
  elseif isa(cur_ast, Function)
    return cur_ast
  else
    @dprintln(1,"typeof(cur_ast) = ", typeof(cur_ast))
    error("Expect either AST or Function after processFuncCall, but got ", cur_ast)
  end
end

"""
A hack to get around Julia's type inference. This is essentially an identity conversion,
but forces inferred return type to be the given type.
Characters coming from C should have Cchar type (which is single byte); Julia can convert them to Char (multi byte).
"""
function identical(::Type{Char}, x::Cchar)
    y::Char = x
    return y
end

identical{T}(::Type{T}, x::T)=x

function createWrapperFuncArgWithType(i, arg::Symbol)
    return Symbol(string("makeWrapperFuncArgument",i))
end

function createWrapperFuncArgWithType(i, arg::Expr)
    assert(arg.head == :(::))
    typ = arg.args[2]
    return Expr(:(::), Symbol(string("makeWrapperFuncArgument",i)), typ)
end

"""
Define a wrapper function with the name given by "new_func" that when called will try to optimize the "real_func" function, and run it with given parameters in "call_sig_args". The input "per_site_opt_set" can be either nothing, or a quoted Expr that refers to an array of OptPass.
"""
function makeWrapperFunc(new_fname::Symbol, real_fname::Symbol, call_sig_args::Array{Any, 1}, per_site_opt_set)
  mod = current_module()
  new_func = GlobalRef(mod, new_fname)
  real_func = GlobalRef(mod, real_fname)
  @dprintln(3, "Create wrapper function ", new_func, " for actual function ", real_func)

  #bt = backtrace() ;
  #s = sprint(io->Base.show_backtrace(io, bt))
  #@dprintln(3, "makeWrapperFunc backtrace ")
  #@dprintln(3, s)

  @dprintln(3, "call_sig_args = ", call_sig_args)
  temp_typs = Any[ typeof(x) for x in tuple(call_sig_args...)]
  temp_tuple = tuple(temp_typs...)
  new_call_sig_args = Symbol[ Symbol(string("makeWrapperFuncArgument",i)) for i = 1:length(call_sig_args)]
  new_call_sig_args_with_types = Any[ createWrapperFuncArgWithType(i, call_sig_args[i]) for i = 1:length(call_sig_args)]
  @dprintln(3, "new_call_sig_args = ", new_call_sig_args)
  @dprintln(3, "new_call_sig_args_with_types = ", new_call_sig_args_with_types)
  @dprintln(3, "call_sig_arg_typs = ", temp_tuple)
  gofd = GlobalRef(CompilerTools.OptFramework, :gOptFrameworkDict)
  proc = GlobalRef(CompilerTools.OptFramework, :processFuncCall)
  dpln = GlobalRef(CompilerTools.OptFramework, :dprintln)
  idtc = GlobalRef(CompilerTools.OptFramework, :identical)
#  if VERSION >= v"0.5.0-dev+5233"
  if VERSION >= v"0.5.0-dev+5381"
    retexpr = Expr(:call, idtc, Expr(:call, GlobalRef(Base, :typeof), :ret), Expr(:call, :func_to_call, new_call_sig_args...))
  else
    retexpr = Expr(:call, idtc, Expr(:static_typeof, :ret), Expr(:call, :func_to_call, new_call_sig_args...))
  end
  wrapper_ast = :(function $new_fname($(new_call_sig_args_with_types...))
         #CompilerTools.OptFramework.@dprintln(3,"new_func running ", $(new_call_sig_args...))
         call_sig_arg_tuple = map(typeof, tuple($(new_call_sig_args...)))
         opt_set = $per_site_opt_set
         fs = ($real_func, call_sig_arg_tuple, opt_set)
         func_to_call = get($gofd, fs, nothing)
         if func_to_call == nothing
           tic()
           process_res = $proc($real_func, call_sig_arg_tuple, opt_set)
           t = toq()
           $dpln(1,$real_func," optimization time = ", t)
           if process_res != nothing
             # We did optimize it in some way we will call the optimized version.
             $dpln(3,"processFuncCall DID optimize ", $real_func)
             func_to_call = process_res
           else
             # We did not optimize it so we will call the original function.
             $dpln(3,"processFuncCall didn't optimize ", $real_func)
             func_to_call = $real_func
           end # Remember this optimization result for this function/type combination.
           $gofd[fs] = func_to_call
         end
         $dpln(3,"calling ", func_to_call)
         if 1 < 0
           ret = $real_func($(new_call_sig_args...))
         end
         #$idtc($static_typeof_ret, func_to_call($(new_call_sig_args...)))
         #func_to_call($(new_call_sig_args...))
         $retexpr
        end)
  @dprintln(4,"wrapper_ast = ", wrapper_ast, " type = ", typeof(wrapper_ast))
  gOptFrameworkDict[new_func] = real_func
  return wrapper_ast
end

type opt_calls_insert_trampoline_state
  per_site_opt_set
  found_callsite

  function opt_calls_insert_trampoline_state(opt_set)
    new(opt_set, false)
  end
end

function invoke_to_call(x, state, top_level_number, is_top_level, read)
  if isa(x, Expr)
    if x.head == :invoke
      return TypedExpr(x.typ, :call, x.args[2:end]...)
    end
  end
  return CompilerTools.AstWalker.ASTWALK_RECURSE
end

"""
An AstWalk callback function.
Finds call sites in the AST and replaces them with calls to newly generated trampoline functions.
These trampolines functions allow us to capture runtime types which in turn enables optimization passes to run on fully typed AST.
If a function/signature combination has not previously been optimized then call processFuncCall to optimize it.
"""
function opt_calls_insert_trampoline(x, state:: opt_calls_insert_trampoline_state, top_level_number, is_top_level, read)
  if typeof(x) == Expr
    if x.head == :call
      # We found a call expression within the larger expression.
      call_expr = x.args[1]          # Get the target of the call.
      call_sig_args = x.args[2:end]  # Get the arguments to the call.
      @dprintln(2, "Start opt_calls = ", call_expr, " signature = ", call_sig_args, " typeof(call_expr) = ", typeof(call_expr))

      # The name of the new trampoline function.
      real_func = Symbol(string(call_expr))

      # Recursively process the arguments to this function possibly finding other calls to replace.
      for i = 2:length(x.args)
        x.args[i] = CompilerTools.AstWalker.AstWalk(x.args[i], opt_calls_insert_trampoline, state)
      end

      trampoline_func = Symbol(string("opt_calls_trampoline_", real_func))
      wrapper_ast = makeWrapperFunc(trampoline_func, real_func, call_sig_args, state.per_site_opt_set) 
      Core.eval(current_module(), wrapper_ast)
      # Update the call expression to call our trampoline and pass the original function so that we can
      # call it if nothing can be optimized.
      x.args = [ trampoline_func; x.args[2:end] ]

      @dprintln(2, "Replaced call_expr = ", call_expr, " type = ", typeof(call_expr), " new = ", x.args[1])

      state.found_callsite = true

      return x
    end    
  end
  return CompilerTools.AstWalker.ASTWALK_RECURSE
end

"""
When @acc is used at a function's callsite, we use AstWalk to search for callsites via the opt_calls_insert_trampoline callback and to then insert trampolines.  
That updated expression containing trampoline calls is then returned as the generated code from the @acc macro.
"""
function convert_expr(per_site_opt_set, ast)
  if is(per_site_opt_set, nothing) && length(optPasses) == 0
    # skip translation since opt_set is empty
    return ast
  else
    @dprintln(2, "convert_expr ", ast, " ", typeof(ast), " per_site_opt_set = ", per_site_opt_set)
    state = opt_calls_insert_trampoline_state(per_site_opt_set)
    res = CompilerTools.AstWalker.AstWalk(ast, opt_calls_insert_trampoline, state)
    @dprintln(2,"converted expression = ", res)

    if state.found_callsite == false
        println("WARNING: @acc macro used on an expression not containing a call-site.")
    end

    return res
  end
end

type WorkItem
  per_site_opt_set
  opt_set
  macros
  ast
end

type MoreWork
  returned_macro_ast
  more_work :: Array{WorkItem,1}
end

"""
When @acc is used at a function definition, it creates a trampoline function, when called with a specific set of signature types, will try to optimize the original function, and call it with the real arguments.  The input "ast" should be an AST of the original function at macro level, which will be   replaced by the trampoline. 
"""
function convert_function(per_site_opt_set, opt_set, macros, ast)
    fname = ast.args[1].args[1]
    assert(isa(fname, Symbol))
    mod = current_module()
    call_sig_args = ast.args[1].args[2:end]
    macro_ast     = deepcopy(ast)
    macro_only    = all(Bool[p.level <= PASS_MACRO for p in opt_set]) || (length(macros) > 0 && macros[1] == Symbol("@inline"))
    real_fname    = gensym(string(fname))
    real_func     = GlobalRef(mod, real_fname)
    macro_fname   = macro_only ? fname : gensym(string(fname))
    macro_func    = GlobalRef(mod, macro_fname)
    ast.args[1].args[1] = real_fname 
    macro_ast.args[1].args[1] = macro_fname 
    work_array = WorkItem[]
    orig_macro_ast_type = typeof(macro_ast)
    @dprintln(3, "@acc convert_function fname = ", fname, " real_fname = ", real_fname, " macro_fname = ", macro_fname)

    @dprintln(3, "@acc converting function = ", macro_ast)
    for i in 1:length(opt_set)
      x = opt_set[i]
      if x.level == PASS_MACRO
        macro_ast = x.func(macro_func, macro_ast, nothing) # macro level transformation only takes input ast as its argument
        if typeof(macro_ast) != orig_macro_ast_type
            @dprintln(3, "Macro pass returned more work = ", macro_ast.more_work)
            assert(typeof(macro_ast) == MoreWork)
            append!(work_array, macro_ast.more_work)
            macro_ast = macro_ast.returned_macro_ast 
        end
        @dprintln(3, "After pass[", i, "], AST = ", macro_ast)
      end
    end
    if length(macros) > 0
       @dprintln(3, "Adding macrocall macros = ", macros)
       ast = Expr(:macrocall, macros..., ast)
       macro_ast = Expr(:macrocall, macros..., macro_ast)
    end
    if !macro_only
      @dprintln(3, "Calling makeWrapperFunc")
      if saveOriginalFunction
          ast = Expr(:block, ast, macro_ast, makeWrapperFunc(fname, macro_fname, call_sig_args, per_site_opt_set))
      else
          ast = Expr(:block, macro_ast, makeWrapperFunc(fname, macro_fname, call_sig_args, per_site_opt_set))
      end
    else
      @dprintln(3, "macro_only conversion")
      if saveOriginalFunction
          ast = Expr(:block, ast, macro_ast)
      else
          ast = Expr(:block, macro_ast)
      end
    end
    @dprintln(3, "macro_func = ", macro_func, " real_func = ", real_func)
    gOptFrameworkDict[macro_func] = real_func

    if !isempty(work_array)
        @dprintln(3, "@acc converting function recursively processing work queue")
    end

    for item in work_array
        @dprintln(3, "@acc work item = ", item)

        item_res = convert_function(item.per_site_opt_set, item.opt_set, item.macros, item.ast)
        assert(is_block(item_res))
        append!(ast.args, item_res.args)
    end

    @dprintln(3, "@acc converting function done = ", ast)
    ast
end

function is_function(expr)
  isa(expr, Expr) && (is(expr.head, :function) || is(expr.head, :(=))) && isa(expr.args[1], Expr) && is(expr.args[1].head, :call)
end

function is_block(expr)
  isa(expr, Expr) && is(expr.head, :block)
end

function is_macro(expr)
  isa(expr, Expr) && is(expr.head, :macrocall)
end

function convert_block(per_site_opt_set, opt_set, macros, ast)
  for i = 1 : length(ast.args)
    @dprintln(3, "@acc processing block element ", i)
    expr = ast.args[i]
    if is_function(expr)
      @dprintln(3, "@acc processing function within block = ", expr)
      ast.args[i] = convert_function(per_site_opt_set, opt_set, macros, expr)
      @dprintln(3, "@acc done processing function within block = ", ast.args[i])
    elseif is_block(expr)
      @dprintln(3, "@acc processing block within block = ", expr)
      ast.args[i] = convert_block(per_site_opt_set, opt_set, macros, expr)
      @dprintln(3, "@acc done processing block within block = ", ast.args[i])
    elseif is_macro(expr)
      @dprintln(3, "@acc processing macro within block = ", expr)
      ast.args[i] = convert_macro(per_site_opt_set, opt_set, macros, expr)
      @dprintln(3, "@acc done processing macro within block = ", ast.args[i])
    else
      @dprintln(3, "Don't know how to process block element[", i, "] of type ", typeof(expr))
      @dprintln(3, "Value = ", expr)
    end
  end
  @dprintln(3, "@acc processing block done = ", ast)
  return ast
end

function convert_macro(per_site_opt_set, opt_set, macros, ast)
  if is_function(ast.args[end])
    macros = vcat(macros, ast.args[1:end-1])
    @dprintln(3, "@acc converting macro function = ", ast, " macros = ", macros)
    convert_function(per_site_opt_set, opt_set, macros, ast.args[end])
  else
    return ast
  end
end

"""
Statically evaluate per-site optimization passes setting, and return the result.
"""
function evalPerSiteOptSet(per_site_opt_set)
  opt_set = Core.eval(current_module(), per_site_opt_set)
  for s in opt_set
    @assert isa(s, OptPass) ("Expect OptPass but got " * dump(s))
  end
  return opt_set
end


"""
The @acc macro comes in two forms:
1) @acc expression
3) @acc function ... end
In the first form, the set of optimization passes to apply come from the default set of optimization passes as specified with the funciton setOptPasses.  The @acc macro replaces each call in the expression with a call to a trampolines that determines the types of the call and if that combination of function and signature has not previously been optimized then it calls the set of optimization passes to optimize it.  Then, the trampoline calls the optimized function.
The second form is similar, and instead annotating callsite, the @acc macro can be used in front of a function's declaration. Used this way, it will replace the body of the function with the trampoline itself. The programmer can use @acc either at function callsite, or at function delcaration, but not both.
This macro may optionally take an OptPass array, right after @acc and followed by an expression or function.  In this case, the specified set of optPasses are used just for optimizing the following expression. When used with the second form (in front of a function), the value of this OptPass array will be statically evaluated at the macro expansion stage.
"""
macro acc(ast1, ast2...)
  if isempty(ast2)
    # default to assume global optPasses setting
    per_site_opt_set = nothing
    ast = ast1
  else
    per_site_opt_set = ast1 
    ast = ast2[1]
  end
  # unlike convert_expr, we must eval per_site_opt_set statically
  opt_set = per_site_opt_set == nothing ? optPasses : evalPerSiteOptSet(per_site_opt_set)
  if !isa(opt_set, Array) || length(opt_set) == 0
    # skip translation since opt_set is empty
  elseif is_function(ast)
    @dprintln(3, "@acc at function level = ", ast)
    # used at function definition
    ast = convert_function(per_site_opt_set, opt_set, Any[], ast)
  elseif is_block(ast)
    @dprintln(3, "@acc at block level = ", ast)
    ast = convert_block(per_site_opt_set, opt_set, Any[], ast)
  elseif is_macro(ast)
    @dprintln(3, "@acc at macro level = ", ast)
    ast = convert_macro(per_site_opt_set, opt_set, Any[], ast)
  else
    # used at call site
    @dprintln(3, "@acc at call-site = ", ast)
    ast = convert_expr(per_site_opt_set, ast)
  end
  @dprintln(4, "@acc done = ", ast)
  esc(ast)
end

"""
Find the optimizing target function (after @acc macro) for a wrapper function in the given module. 
Return the input function if not found. Always return as a GlobalRef.
"""
function findTargetFunc(mod::Module, name::Symbol)
   func = GlobalRef(mod, name)
   get(gOptFrameworkDict, func, func) :: GlobalRef
end

"""
Find the original (before @acc macro) function for a wrapper function in the given module. 
Return the input function if not found. Always return as a GlobalRef.
"""
function findOriginalFunc(mod::Module, name::Symbol)
   func = GlobalRef(mod, name)
   orig = get(gOptFrameworkDict, func, func)
   # we lookup twice because the redirection goes like this: wrapper -> macro -> ast
   get(gOptFrameworkDict, orig, orig) :: GlobalRef
end

function recursive_noacc(ast::Symbol)
   if haskey(gOptFrameworkDict, GlobalRef(current_module(), ast))
     findOriginalFunc(current_module(), ast)
   else
     ast
   end
end

function recursive_noacc(ast::Expr)
    start = 1
    if is(ast.head, :(=))
      start = 2
    elseif is(ast.head, :call) && isa(ast.args[1], Symbol)  
      ast.args[1] = recursive_noacc(ast.args[1])
      start = 2
    end
    for i = start:length(ast.args)
      ast.args[i] = recursive_noacc(ast.args[i])
    end
    return ast 
end

function recursive_noacc(ast::ANY)
    ast
end

"""
The macro @noacc can be used at call site to specifically run the non-accelerated copy of an accelerated function. It has no effect and gives a warning when the given function is not found to have been accelerated. We do not support nested @acc or @noacc. 
"""
macro noacc(ast)
  ast = recursive_noacc(ast)
  esc(ast)
end


end   # end of module
