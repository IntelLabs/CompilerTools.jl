module OptFramework

using CompilerTools

export @acc 

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

type optPass
    func :: Function
    lowered :: Bool   # uses unoptimized code_typed form

    function optPass(f, l)
      new (f, l)
    end
end

optPasses = optPass[]

function setOptPasses(passes :: Array{optPass,1} )
    lowered_first = true

    for i = 1:length(passes)
      if passes[i].lowered == true
        if lowered_first == false
          throw(string("Optimization passes cannot handle a lowered AST pass after a typed AST pass."))
        end
      else
        lowered_first = false
      end
    end

    global optPasses = passes
end

function typeOfOpr(x)
#  dprintln(3,"typeOfOpr ", x, " type = ", typeof(x))
  if isa(x, Expr) x.typ
  elseif isa(x, SymbolNode) x.typ
  else typeof(x) 
  end
end   

type memoizeState
  mapNameFuncInfo :: Dict{Any, Any}   # tracks the mapping from unoptimized function name to optimized function name
  trampolineSet   :: Set{Any}         # tracks whether we've previously created a trampoline for a given function name and signature
  per_site_opt_set

  function memoizeState()
    new (Dict{Any,Any}(), Set{Any}(), nothing)
  end
end

type lmstate
  label_map
  next_block_num
  last_was_label

  function lmstate()
    new (Dict{Int64,Int64}(), 0, false)
  end
end

function update_labels(x, state :: lmstate, top_level_number, is_top_level, read)
  asttyp = typeof(x)
  if asttyp == LabelNode
    return LabelNode(state.label_map[x.label])
  elseif asttyp == GotoNode
    return GotoNode(state.label_map[x.label])
  elseif asttyp == Expr
    head = x.head
    args = x.args
    if head == :gotoifnot
      else_label = args[2]
      x.args[2] = state.label_map[else_label]
      return x
    end
  end
  return nothing
end

function create_label_map(x, state :: lmstate, top_level_number, is_top_level, read)
  asttyp = typeof(x)
  if asttyp == LabelNode
    if state.last_was_label
      state.label_map[x.label] = state.next_block_num-1
    else
      state.label_map[x.label] = state.next_block_num
      state.next_block_num += 1
    end
    state.last_was_label = true
  else
    state.last_was_label = false
  end
  return nothing
end

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

function tfuncPresent(func, tt)
  m = methods(func, tt)[1]
  def = m.func.code
  if def.tfunc == ()
    dprintln(1, "tfunc NOT present before code_typed")
    code_typed(func, tt)
    if def.tfunc == ()
      dprintln(1, "tfunc NOT present after code_typed")
    else
      dprintln(1, "tfunc present after code_typed")
    end
  else
    dprintln(1, "tfunc present on call")
  end 
end

function loweredToTyped(func :: Function, loweredAst, call_sig_arg_tuple)
  new_func_name = string(string(func), "_loweredToTyped")
  nfsym = symbol(new_func_name)
  assert(typeof(loweredAst) == Expr && loweredAst.head == :lambda)
  copy_args = loweredAst.args[1]
  body = loweredAst.args[3]
  assert(typeof(body) == Expr && body.head == :body)
  dprintln(2,"loweredToTyped typeof(copy_args) = ", typeof(copy_args), " ", copy_args)
  dprintln(2,"loweredToTyped typeof(loweredAst.args[3]) = ", typeof(loweredAst.args[3]), " ", loweredAst.args[3])
  state = lmstate()
  CompilerTools.AstWalker.AstWalk(body, create_label_map, state)
  #dprintln(3,"label mapping = ", state.label_map)
  state.last_was_label = false
  loweredAst.args[3] = CompilerTools.AstWalker.get_one(CompilerTools.AstWalker.AstWalk(loweredAst.args[3], update_labels, state))
  loweredAst.args[3].args = removeDupLabels(loweredAst.args[3].args)
  new_func = Expr(:function, Expr(:call, nfsym, copy_args...), Expr(:block, loweredAst.args[3].args...))
  dprintln(2,"loweredToTyped new body = ", loweredAst.args[3])
  eval_new_func = Base.function_module(func, call_sig_arg_tuple).eval(new_func)
  if DEBUG_LVL >= 3
    lambda = code_lowered(eval_new_func, call_sig_arg_tuple)[1]
    println("lowered copy = \n", lambda)
  end
  return code_typed(eval_new_func, call_sig_arg_tuple)[1]
end

function copyFunctionNewName(old_func, new_func_name :: String, arg_tuple)
  lambda = code_lowered(old_func, arg_tuple)[1]
  nfsym = symbol(new_func_name)
  dprintln(3, "copying old_func = \n", lambda)

  copy_args = lambda.args[1]
  copy_body = lambda.args[3].args
  dprintln(3,"copyFunctionNewName body = \n", lambda.args[3])
  state = lmstate()
  CompilerTools.AstWalker.AstWalk(lambda.args[3], create_label_map, state)
  #dprintln(3,"label mapping = ", state.label_map)
  state.last_was_label = false
  lambda.args[3] = CompilerTools.AstWalker.get_one(CompilerTools.AstWalker.AstWalk(lambda.args[3], update_labels, state))
  copy_body = lambda.args[3].args = removeDupLabels(lambda.args[3].args)
  #dprintln(3,"after label renumberingl = \n", lambda.args[3], " type = ", typeof(lambda.args[3]), " copy_body = ", copy_body, " type = ", typeof(copy_body))
 
  new_func = Expr(:function, Expr(:call, nfsym, copy_args...), Expr(:block, copy_body...))
  eval_new_func = Base.function_module(old_func, arg_tuple).eval(new_func)
  #eval_new_func = Base.function_module(old_func).eval(new_func)
  if DEBUG_LVL >= 3
    lambda = code_lowered(eval_new_func, arg_tuple)[1]
    dprintln(3, "new copied func = \n", lambda)
    tfuncPresent(eval_new_func, arg_tuple)
  end
  code_typed(eval_new_func, arg_tuple) # force tfunc to be created in methods[1].func.code
  return eval_new_func
end

function processFuncCall(func_expr, call_sig_arg_tuple, call_sig_args, per_site_opt_set)
  fetyp = typeof(func_expr)

  dprintln(3,"processFuncCall ", func_expr, " module = ", Base.function_module(func_expr, call_sig_arg_tuple), " ", call_sig_arg_tuple, " ", fetyp, " args = ", call_sig_args, " opt_set = ", per_site_opt_set)
  func = eval(func_expr)
  dprintln(3,"func = ", func, " type = ", typeof(func))

  ftyp = typeof(func)
  dprintln(4,"After name resolution: func = ", func, " type = ", ftyp)
  if ftyp == DataType
    return nothing
  end
  assert(ftyp == Function || ftyp == IntrinsicFunction || ftyp == LambdaStaticData)

  # If per site opt set has not been provided then use the global default.
  if per_site_opt_set == nothing
    per_site_opt_set = optPasses
  else
    assert(isa(per_site_opt_set, Array))
    for s in per_site_opt_set
      assert(typeof(s) == optPass)
    end
  end

  if ftyp == Function
    #fs = (func, call_sig_arg_tuple)

    if length(per_site_opt_set) == 0
      throw(string("There are no registered optimization passes."))
    end

    new_func_name = string(string(func),"_processFuncCall")
    new_func = copyFunctionNewName(func, new_func_name, call_sig_arg_tuple)
    dprintln(2,"temp_func is ", new_func)
    # Force tfunc to instantiate so that we can over-write it later at the end of optimization.
    #precompile(new_func, call_sig_arg_tuple)

    #new_func = deepcopy(func)

    last_lowered = per_site_opt_set[1].lowered

    # Get the AST on which the first optimization pass wants to work.
    if last_lowered == true
      cur_ast = code_typed(new_func, call_sig_arg_tuple, optimize=false)[1]   # false means generate type information but don't otherwise optimize
      #cur_ast = code_lowered(new_func, call_sig_arg_tuple)[1]
    else
      cur_ast = code_typed(new_func, call_sig_arg_tuple)[1]
    end
    assert(typeof(cur_ast) == Expr)
    assert(cur_ast.head == :lambda)

    dprintln(3,"Initial code to optimize = ", cur_ast)

    for i = 1:length(per_site_opt_set)
      if per_site_opt_set[i].lowered != last_lowered
        cur_ast = loweredToTyped(new_func, cur_ast, call_sig_arg_tuple)
      end
      last_lowered = per_site_opt_set[i].lowered
      assert(typeof(cur_ast) == Expr && cur_ast.head == :lambda)
      assert(typeof(cur_ast.args[3]) == Expr && cur_ast.args[3].head == :body)

      cur_ast = per_site_opt_set[i].func(cur_ast, call_sig_arg_tuple, call_sig_args)

      assert(typeof(cur_ast) == Expr && cur_ast.head == :lambda)
      assert(typeof(cur_ast.args[3]) == Expr && cur_ast.args[3].head == :body)

      if typeof(cur_ast) == Function
        dprintln(3,"Optimization pass returned a function.")
        if i != length(per_site_opt_set)
          dprintln(0,"A non-final optimization pass returned a Function so later optimization passes will not run.")
        end
        return cur_ast
      else
        dprintln(3,"AST after optimization pass ", i, " = ", cur_ast)
        if typeof(cur_ast) != Expr
          dprintln(0, "cur_ast after opt pass not an expression. type = ", typeof(cur_ast))
        end
      end
    end

    if last_lowered == true
      assert(typeof(cur_ast) == Expr && cur_ast.head == :lambda)
      assert(typeof(cur_ast.args[3]) == Expr && cur_ast.args[3].head == :body)
      body = cur_ast.args[3]
      dprintln(3,"Last opt pass worked on lowered.\n", body)

      cur_ast = loweredToTyped(new_func, cur_ast, call_sig_arg_tuple)

      assert(typeof(cur_ast) == Expr && cur_ast.head == :lambda)
      assert(typeof(cur_ast.args[3]) == Expr && cur_ast.args[3].head == :body)

      body = cur_ast.args[3]
      dprintln(3,"Last opt pass after converting to typed AST.\n", body)
    end

    # Write the modifed code back to the function.
    dprintln(2,"Before methods at end of processFuncCall.")
    tfuncPresent(new_func, call_sig_arg_tuple)
    method = methods(new_func, call_sig_arg_tuple)
    assert(length(method) == 1)
    method = method[1]
    method.func.code.tfunc[2] = ccall(:jl_compress_ast, Any, (Any,Any), method.func.code, cur_ast)

    dprintln(3,"Final processFuncCall = ", code_typed(new_func, call_sig_arg_tuple)[1])
    return new_func
  end
  return nothing
end

gOptFrameworkState = memoizeState()

function opt_calls_insert_trampoline(x, state :: memoizeState, top_level_number, is_top_level, read)
  if typeof(x) == Expr
    if x.head == :call
      # We found a call expression within the larger expression.
      call_expr = x.args[1]
      call_sig_args = x.args[2:end]
      dprintln(2, "Start opt_calls = ", call_expr, " signature = ", call_sig_args, " typeof(call_expr) = ", typeof(call_expr))

      # The name of the new trampoline function.
      new_func_name = string("opt_calls_trampoline_", string(call_expr))
      new_func_sym  = symbol(new_func_name)

      # Recursively process the arguments to this function possibly finding other calls to replace.
      for i = 2:length(x.args)
        new_arg = CompilerTools.AstWalker.AstWalk(x.args[i], opt_calls_insert_trampoline, state)
        assert(isa(new_arg,Array))
        assert(length(new_arg) == 1)
        x.args[i] = new_arg[1]
      end

      # Form a tuple of the function name and arguments.
      # FIX?  These are the actual arguments so it is likely this won't memoize anything.
      tmtup = (call_expr, call_sig_args)
#      if !in(tmtup, state.trampolineSet)
        # We haven't created a trampoline for this function call yet.
        dprintln(3,"Creating new trampoline for ", call_expr)
        # Remember that we've created a trampoline for this pair.
#        push!(state.trampolineSet, tmtup)
        dprintln(2, new_func_sym)
        for i = 1:length(call_sig_args)
          dprintln(2, "    ", call_sig_args[i])
        end
        per_site_opt_set = state.per_site_opt_set 
 
       # Define the trampoline.
       @eval function ($new_func_sym)(orig_func, per_site_opt_set, $(call_sig_args...))
              # Create a tuple of the actual argument types for this invocation.
              call_sig = Expr(:tuple)
              call_sig.args = map(typeOfOpr, Any[ $(call_sig_args...) ]) 
              call_sig_arg_tuple = eval(call_sig)
              #println(call_sig_arg_tuple)

              # Create a tuple of function and argument types.
              fs = ($new_func_sym, call_sig_arg_tuple, per_site_opt_set)
              dprintln(1, "running ", $new_func_name, " fs = ", fs)

              # If we have previously optimized this function and type combination ...
              if haskey(gOptFrameworkState.mapNameFuncInfo, fs)
                # ... then call the function we previously optimized.
                func_to_call = gOptFrameworkState.mapNameFuncInfo[fs]
              else
                # ... else see if we can optimize it.
                process_res = processFuncCall(orig_func, call_sig_arg_tuple, $call_sig_args, per_site_opt_set)

                if process_res != nothing
                  # We did optimize it in some way we will call the optimized version.
                  dprintln(3,"processFuncCall DID optimize ", orig_func)
                  func_to_call = process_res
                else
                  # We did not optimize it so we will call the original function.
                  dprintln(3,"processFuncCall didn't optimize ", orig_func)
                  func_to_call = orig_func
                end
                # Remember this optimization result for this function/type combination.
                gOptFrameworkState.mapNameFuncInfo[fs] = func_to_call
              end

              dprintln(1, "Executing function = ", Base.function_name(func_to_call), " module = ", Base.function_module(func_to_call, call_sig_arg_tuple))
              #dprintln(3,"Code to call = ", code_typed(func_to_call, call_sig_arg_tuple)[1])
              # Call the function.
              ret = func_to_call($(call_sig_args...))
              #dprintln(3,"Code to call after = ", code_typed(func_to_call, call_sig_arg_tuple)[1])
              ret
            end
#      end

      # Update the call expression to call our trampoline and pass the original function so that we can
      # call it if nothing can be optimized.
      resolved_name = @eval OptFramework.$new_func_sym
      x.args = [ resolved_name; call_expr; per_site_opt_set; x.args[2:end] ]

      dprintln(2, "Replaced call_expr = ", call_expr, " type = ", typeof(call_expr), " new = ", x.args[1])

      return x
    end    
  end
  nothing
end

# Replacing function calls in the expr passed to the macro with trampoline calls.
function convert_expr(ast)
  dprintln(2, "Mtest ", ast, " ", typeof(ast), " gOptFrameworkState = ", gOptFrameworkState)
  res = CompilerTools.AstWalker.AstWalk(ast, opt_calls_insert_trampoline, gOptFrameworkState)
  assert(isa(res,Array))
  assert(length(res) == 1)
  dprintln(2,"converted expression = ", res[1])
  return esc(res[1])
end

macro acc(ast1, ast2...)
  if isempty(ast2)
#    println("old acc code")
    gOptFrameworkState.per_site_opt_set = nothing
    return convert_expr(ast1)
  else
#    println("new acc code")
    gOptFrameworkState.per_site_opt_set = ast1
    return convert_expr(ast2[1]) 
  end
end


function foo(x)
  println("foo = ", x, " type = ", typeof(x))
  z1 = zeros(100)
  sum = 0.0
  for i = 1:100
    sum = sum + z1[i] 
  end
#  bt = backtrace()
#  Base.show_backtrace(STDOUT, bt)
#  println("")
  x+1
end

function foo2(x,y)
  println("foo2")
  x+y
end

function foo_new(x)
  println("foo_new = ", x)
  x+10
end

function bar(x)
  println("bar = ", x)

  z1 = zeros(100)
  sum = 0.0
  for i = 1:100
    sum = sum + z1[i] 
  end

  x+2
end

function bar_new(x)
  println("bar_new = ", x)
  x+20
end

function testit()
#y = 1
z = 7
#@acc y = foo(bar(y))
#println(macroexpand(quote @acc y = foo(z) end))
#@acc y = foo(z)
#@acc y = foo(y)
println(y)
#processFuncCall(foo, (Int64,))
#convert_expr(quote y = foo(z) end)
end

#testit()

end   # end of module
