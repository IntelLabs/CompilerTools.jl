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
  dprintln(2, "Add optimization pass at level ", dumpLevel(pass.level))
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
function getCodeAtLevel(func, sig, level)
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
  dprintln(3, "getCodeAtLevel ", dumpLevel(level), " ast = ", ast)
  @assert (length(ast) > 0) ("Failed to retrieve AST for function " * dump(func) * " with signature " * dump(sig))
  @assert (length(ast) == 1) ("Expect one AST but got many for function " * dump(func) * " with signature " * dump(sig) * ": " * dump(ast))
  @assert (isa(ast[1], Expr) && ast[1].head == :lambda) ("Expect Expr with :lambda head, but got " * dump(ast[1]))
  dprintln(3, "getCodeAtLevel returns")
  return ast[1]
end

"""
convert AST from "old_level" to "new_level". The input "ast" can be either Expr or Function type. In the latter case, the result AST will be obtained from this function using an matching signature "sig". The last "func" is a skeleton function that is used internally to facility such conversion.
"""
function convertCodeToLevel(ast :: ANY, sig :: ANY, old_level, new_level, func)
  dprintln(3,"convertCodeToLevel sig = ", sig, " ", old_level, "=>", new_level, " func = ", func, " typeof(sig) = ", typeof(sig))
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
    @assert (isa(lambda, LambdaStaticData)) ("LambdaStaticData not found for " * func * " of signature " * sig)
    lambda.ast = ccall(:jl_compress_ast, Any, (Any,Any), lambda, ast)
    if new_level == PASS_UNOPTTYPED
      dprintln(3,"Calling lambdaTypeinf with optimize=false")
      (new_ast, rty) = CompilerTools.LambdaHandling.lambdaTypeinf(lambda, sig, optimize=false)
    else
      assert(new_level == PASS_TYPED)
      dprintln(3,"Calling lambdaTypeinf with optimize=true")
      dprintln(4,"lambda = ", lambda)
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
The callback state variable used by create_label_map and update_labels.
label_map is a dictionary mapping old label ID's in the old AST with new label ID's in the new AST.
next_block_num is a monotonically increasing integer starting from 0 so label occur sequentially in the new AST.
last_was_label keeps track of whether we see two consecutive LabelNodes in the AST.
"""
type lmstate
  label_map
  next_block_num
  last_was_label

  function lmstate()
    new(Dict{Int64,Int64}(), 0, false)
  end
end

"""
An AstWalk callback that applies the label map created during create_label_map AstWalk.
For each label in the code, replace that label with the rhs of the label map.
"""
function update_labels(x::LabelNode, state :: lmstate, top_level_number, is_top_level, read)
    return LabelNode(state.label_map[x.label])
end

function update_labels(x::GotoNode, state :: lmstate, top_level_number, is_top_level, read)
    return GotoNode(state.label_map[x.label])
end

function update_labels(x::Expr, state :: lmstate, top_level_number, is_top_level, read)
    head = x.head
    args = x.args
    if head == :gotoifnot
      else_label = args[2]
      x.args[2] = state.label_map[else_label]
      return x
    end
    return CompilerTools.AstWalker.ASTWALK_RECURSE
end

function update_labels(x::ANY, state :: lmstate, top_level_number, is_top_level, read)
    return CompilerTools.AstWalker.ASTWALK_RECURSE
end


"""
An AstWalk callback that collects information about labels in an AST.
The labels in AST are generally not sequential but to feed back into a Function Expr
correctly they need to be.  So, we keep a map from the old label in the AST to a new label
that we monotonically increases.
If we have code in the AST like the following:
   1:
   2:
... then one of these labels is redundant.  We set "last_was_label" if the last AST node
we saw was a label.  If we see another LabelNode right after that then we duplicate the rhs
of the label map.  For example, if you had the code:
   5:
   4:
... and the label 5 was the third label in the code then in the label map you would then have:
   5 -> 3, 4 -> 3.
This indicates that uses of both label 5 and label 4 in the code will become label 3 in the modified AST.
"""
function create_label_map(x::LabelNode, state :: lmstate, top_level_number, is_top_level, read)
    if state.last_was_label
      state.label_map[x.label] = state.next_block_num-1
    else
      state.label_map[x.label] = state.next_block_num
      state.next_block_num += 1
    end
    state.last_was_label = true
    return CompilerTools.AstWalker.ASTWALK_RECURSE
end

function create_label_map(x::ANY, state :: lmstate, top_level_number, is_top_level, read)
    state.last_was_label = false
    return CompilerTools.AstWalker.ASTWALK_RECURSE
end

"""
Sometimes update_labels creates two label nodes that are the same.
This function removes such duplicate labels.
"""
function removeDupLabels(stmts)
  if length(stmts) == 0
    return Any[]
  end

  ret = Any[]

  push!(ret, stmts[1])

  for i = 2:length(stmts)
    if !(typeof(stmts[i]) == LabelNode && typeof(stmts[i-1]) == LabelNode)
      push!(ret, stmts[i])
    end
  end

  ret
end

"""
Clean up the labels in AST by renaming them, and removing duplicates.
"""
function cleanupASTLabels(ast)
  assert(isa(ast, Expr) && ast.head == :lambda)
  body = ast.args[3]
  assert(typeof(body) == Expr && body.head == :body)
  state = lmstate()
  CompilerTools.AstWalker.AstWalk(body, create_label_map, state)
  #dprintln(3,"label mapping = ", state.label_map)
  state.last_was_label = false
  body = CompilerTools.AstWalker.AstWalk(body, update_labels, state)
  body.args = removeDupLabels(body.args)
  ast.args[3] = body
  return ast
end

"""
Makes sure that a newly created function is correctly present in the internal Julia method table.
"""
function tfuncPresent(func, tt)
  m = methods(func, tt)[1]
  def = m.func.code
  if is(def.tfunc, nothing)
    dprintln(2, "tfunc NOT present before code_typed")
    code_typed(func, tt)
    if is(def.tfunc, nothing) 
      error("tfunc still NOT present after code_typed")
    else
      dprintln(2, "tfunc present after code_typed")
    end
  else
    dprintln(2, "tfunc present on call")
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
  dprintln(3,"processFuncCall starting = ", func, " call_sig_arg_tuple = ", call_sig_arg_tuple)
  @assert (isa(func, Function)) ("processFuncCall can only optimize functions, but got " * typeof(func))
  if per_site_opt_set == nothing 
    per_site_opt_set = optPasses 
  end
  @assert (length(per_site_opt_set) > 0) "There are no registered optimization passes."
  func_module = Base.function_module(func, call_sig_arg_tuple)
  func_ref = GlobalRef(func_module, symbol(string(func)))
  dprintln(3,"processFuncCall ", func_ref, " ", call_sig_arg_tuple, " opt_set = ", per_site_opt_set)

  # Create a skeleton of the incoming function, which is used to facilitate AST conversion, and will eventually be the result function to be returned.
  new_func_name = gensym(string(func_ref))
  fake_args = Any[ gensym() for a in call_sig_arg_tuple ]
  new_func = Core.eval(func_module, :(function $(new_func_name)($(fake_args...)) end))
  dprintln(2,"temp_func is ", new_func)

  # Remember what level the AST was in.
  cur_level = per_site_opt_set[1].level
  cur_ast = func

  dprintln(3,"Initial code to optimize = ", cur_ast)

  # For each optimization pass in the optimization set.
  for i = 1:length(per_site_opt_set)
      dprintln(3,"optimization pass ", i)
      # See if the current optimization pass uses optimized AST form and the previous optimization pass used unoptimized AST form.
      cur_level = per_site_opt_set[i].level
      if cur_level > PASS_MACRO
        cur_ast = convertCodeToLevel(cur_ast, call_sig_arg_tuple, cur_level, cur_level, new_func)
        assert(typeof(cur_ast.args[3]) == Expr && cur_ast.args[3].head == :body)
        # Call the current optimization on the current AST.
        cur_ast = per_site_opt_set[i].func(func_ref, cur_ast, call_sig_arg_tuple)
        dprintln(3,"AST after optimization pass ", i, " = ", cur_ast)
      end
  end

  dprintln(3,"After optimization passes")

  if isa(cur_ast, Expr)
    ast = convertCodeToLevel(cur_ast, call_sig_arg_tuple, cur_level, PASS_TYPED, new_func)
    dprintln(3,"Last opt pass after converting to typed AST.\n", cur_ast.args[3])

    # Write the modifed code back to the function.
    dprintln(2,"Before methods at end of processFuncCall.")
    tfuncPresent(new_func, call_sig_arg_tuple)
    method = methods(new_func, call_sig_arg_tuple)
    assert(length(method) == 1)
    method = method[1]
    method.func.code.tfunc[2] = ccall(:jl_compress_ast, Any, (Any,Any), method.func.code, cur_ast)

    dprintln(3,"Final processFuncCall = ", code_typed(new_func, call_sig_arg_tuple)[1])
    return new_func
  elseif isa(cur_ast, Function)
    return cur_ast
  else
    error("Expect either AST or Function after processFuncCall, but got ", cur_ast)
  end
end

"""
A hack to get around Julia's type inference. This is essentially an identity conversion,
but forces inferred return type to be the given type.
"""
identical{T}(t::Type{T}, x::T)=x

"""
Define a wrapper function with the name given by "new_func" that when called will try to optimize the "real_func" function, and run it with given parameters in "call_sig_args". The input "per_site_opt_set" can be either nothing, or a quoted Expr that refers to an array of OptPass.
"""
function makeWrapperFunc(new_fname::Symbol, real_fname::Symbol, call_sig_args::Array{Any, 1}, per_site_opt_set)
  mod = current_module()
  new_func = GlobalRef(mod, new_fname)
  real_func = GlobalRef(mod, real_fname)
  dprintln(3, "Create wrapper function ", new_func, " for actual function ", real_func)

  #bt = backtrace() ;
  #s = sprint(io->Base.show_backtrace(io, bt))
  #dprintln(3, "makeWrapperFunc backtrace ")
  #dprintln(3, s)

  dprintln(3, "call_sig_args = ", call_sig_args)
  temp_typs = Any[ typeof(x) for x in tuple(call_sig_args...)]
  temp_tuple = tuple(temp_typs...)
  new_call_sig_args = Symbol[ symbol("makeWrapperFuncArgument",i) for i = 1:length(call_sig_args)]
  dprintln(3, "new_call_sig_args = ", new_call_sig_args)
  dprintln(3, "call_sig_arg_typs = ", temp_tuple)
  static_typeof_ret = Expr(:static_typeof, :ret)
  gofd = GlobalRef(CompilerTools.OptFramework, :gOptFrameworkDict)
  proc = GlobalRef(CompilerTools.OptFramework, :processFuncCall)
  dpln = GlobalRef(CompilerTools.OptFramework, :dprintln)
  idtc = GlobalRef(CompilerTools.OptFramework, :identical)
  wrapper_ast = :(function $new_fname($(new_call_sig_args...))
         #CompilerTools.OptFramework.dprintln(3,"new_func running ", $(new_call_sig_args...))
         call_sig_arg_typs = Any[ typeof(x) for x in tuple($(new_call_sig_args...)) ]
         call_sig_arg_tuple = tuple(call_sig_arg_typs...)
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
           end
           # Remember this optimization result for this function/type combination.
           $gofd[fs] = func_to_call
         end
         $dpln(3,"calling ", func_to_call)
         if 1 < 0
           ret = $real_func($(new_call_sig_args...))
         end
         $idtc($static_typeof_ret, func_to_call($(new_call_sig_args...)))
        end)
  dprintln(4,"wrapper_ast = ", wrapper_ast)
  gOptFrameworkDict[new_func] = real_func
  return wrapper_ast
end

"""
An AstWalk callback function.
Finds call sites in the AST and replaces them with calls to newly generated trampoline functions.
These trampolines functions allow us to capture runtime types which in turn enables optimization passes to run on fully typed AST.
If a function/signature combination has not previously been optimized then call processFuncCall to optimize it.
"""
function opt_calls_insert_trampoline(x, per_site_opt_set, top_level_number, is_top_level, read)
  if typeof(x) == Expr
    if x.head == :call
      # We found a call expression within the larger expression.
      call_expr = x.args[1]          # Get the target of the call.
      call_sig_args = x.args[2:end]  # Get the arguments to the call.
      dprintln(2, "Start opt_calls = ", call_expr, " signature = ", call_sig_args, " typeof(call_expr) = ", typeof(call_expr))

      # The name of the new trampoline function.
      real_func = symbol(string(call_expr))

      # Recursively process the arguments to this function possibly finding other calls to replace.
      for i = 2:length(x.args)
        x.args[i] = CompilerTools.AstWalker.AstWalk(x.args[i], opt_calls_insert_trampoline, per_site_opt_set)
      end

      trampoline_func = symbol(string("opt_calls_trampoline_", real_func))
      wrapper_ast = makeWrapperFunc(trampoline_func, real_func, call_sig_args, per_site_opt_set) 
      Core.eval(current_module(), wrapper_ast)
      # Update the call expression to call our trampoline and pass the original function so that we can
      # call it if nothing can be optimized.
      x.args = [ trampoline_func; x.args[2:end] ]

      dprintln(2, "Replaced call_expr = ", call_expr, " type = ", typeof(call_expr), " new = ", x.args[1])

      return x
    end    
  end
  return CompilerTools.AstWalker.ASTWALK_RECURSE
end

"""
When @acc is used at a function's callsite, we use AstWalk to search for callsites via the opt_calls_insert_trampoline callback and to then insert trampolines.  That updated expression containing trampoline calls is then returned as the generated code from the @acc macro.
"""
function convert_expr(per_site_opt_set, ast)
  if is(per_site_opt_set, nothing) && length(optPasses) == 0
    # skip translation since opt_set is empty
    return ast
  else
    dprintln(2, "convert_expr ", ast, " ", typeof(ast), " per_site_opt_set = ", per_site_opt_set)
    res = CompilerTools.AstWalker.AstWalk(ast, opt_calls_insert_trampoline, per_site_opt_set)
    dprintln(2,"converted expression = ", res)
    return res
  end
end

"""
When @acc is used at a function definition, it creates a trampoline function, when called with a specific set of signature types, will try to optimize the original function, and call it with the real arguments.  The input "ast" should be an AST of the original function at macro level, which will be   replaced by the trampoline. 
"""
function convert_function(per_site_opt_set, opt_set, macros, ast)
    fname = ast.args[1].args[1]
    assert(isa(fname, Symbol))
    mod = current_module()
    call_sig_args = ast.args[1].args[2:end]
    macro_ast = deepcopy(ast)
    macro_only = all(Bool[p.level <= PASS_MACRO for p in opt_set]) || (length(macros) > 0 && macros[1] == symbol("@inline"))
    real_fname = gensym(string(fname))
    real_func = GlobalRef(mod, real_fname)
    macro_fname = macro_only ? fname : gensym(string(fname))
    macro_func = GlobalRef(mod, macro_fname)
    ast.args[1].args[1] = real_fname 
    macro_ast.args[1].args[1] = macro_fname 
    dprintln(3, "Initial code = ", ast)
    for i in 1:length(opt_set)
      x = opt_set[i]
      if x.level == PASS_MACRO
        macro_ast = x.func(macro_func, macro_ast, nothing) # macro level transformation only takes input ast as its argument
        dprintln(3, "After pass[", i, "], AST = ", macro_ast)
      end
    end
    if length(macros) > 0
       ast = Expr(:macrocall, macros..., ast)
       macro_ast = Expr(:macrocall, macros..., macro_ast)
    end
    if !macro_only
      ast = Expr(:block, ast, macro_ast, makeWrapperFunc(fname, macro_fname, call_sig_args, per_site_opt_set))
    else
      ast = Expr(:block, ast, macro_ast)
    end
    gOptFrameworkDict[macro_func] = real_func
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
    expr = ast.args[i]
    if is_function(expr)
      ast.args[i] = convert_function(per_site_opt_set, opt_set, macros, expr)
    elseif is_block(expr)
      ast.args[i] = convert_block(per_site_opt_set, opt_set, macros, expr)
    elseif is_macro(expr)
      ast.args[i] = convert_macro(per_site_opt_set, opt_set, macros, expr)
    end
  end
  return ast
end

function convert_macro(per_site_opt_set, opt_set, macros, ast)
  if is_function(ast.args[end])
    macros = vcat(macros, ast.args[1:end-1])
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
    # used at function definition
    ast = convert_function(per_site_opt_set, opt_set, Any[], ast)
  elseif is_block(ast)
    ast = convert_block(per_site_opt_set, opt_set, Any[], ast)
  elseif is_macro(ast)
    ast = convert_macro(per_site_opt_set, opt_set, Any[], ast)
  else
    # used at call site
    ast = convert_expr(per_site_opt_set, ast)
  end
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
