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


module Traversal

export traverse, fold, build, fmap
export getSymbols, normalize, substSymbols

# A generic immutable traversal based on recursion schemes.
# One only has to define a method of fmap (aka Functor) for a custom type in order to traverse it.

# traverse :: Functor f => ((f a -> f b) -> a -> b) -> a -> b
# traverse h e = h (fmap (traverse h)) e

# fold  g = traverse (\h -> g . h . out)
# build g = traverse (\h -> in . h . g)

# out :: Functor f => a -> f a
# in  :: Functor f => f a -> a

traverse(h, e) = h(e -> fmap(x -> traverse(h, x), e), e)
fold(g, e)  = traverse((h, e) -> g(h(e)), e)
build(g, e) = traverse((h, e) -> h(g(e)), e)

typed_expr(typ, head, args) = begin z = Expr(head); z.args = args; z.typ = typ; z end

fmap(f, e::Expr)  = typed_expr(fmap(f, e.typ), fmap(f, e.head), fmap(f, e.args))
fmap(f, e::Array) = [ f(x) for x in e ]
fmap(f, e::Any)   = e

# Example 1: count number of leaf nodes (non-Expr, and non-Array) in an AST.
# sum_expr(e::Expr)  = e.head + sum(e.args)
# sum_expr(e::Array) = length(e) == 0 ? 0 : sum(e)
# sum_expr(e::Any)   = 1
# count(e) = fold(sum_expr, e)


"""
Collect all symbols in an Expr, and we skip Symbols that occur in Types, and in the type 
position of Expr x::T. 
"""
function getSymbols(e)
  syms = Set{Symbol}()
  process(h, e::Symbol) = begin push!(syms, e); e end
  process(h, e::Slot) = begin push!(syms, e.id); e end
  process(h, e::Type) = e
  process(h, e::Expr) = if e.head == :(::) h(e.args[1]) else h(e) end
  process(h, e::Any) = h(e)
  traverse(process, e)
  return syms
end

# Example 2: flattern/normalize nested expressions by assigning them to temporary variables
type State
  params
  varinfo 
  body
  parent
  level :: Int
end

function newlocal(state::State, typ)
  n = length(state.varinfo[3])
  push!(state.varinfo[3], typ)
  return GenSym(n)
end

function emit(state::State, stmt)
  push!(state.body, stmt)
end

"""
Normalize nested Exprs such that all arguments for Expr(:call, ...) will 
be replaced by freshly created GenSyms if they are Exprs. 

The input must be an Expr(:lambda, ...).
"""
function normalize(e) 
  state = State(nothing, nothing, nothing, nothing, -1)
  function process(h, e::Expr)
    state.level = state.level + 1
    if e.head == :lambda
      params = e.args[1]
      varinfo = deepcopy(e.args[2])
      body = e.args[3]
      state = State(params, varinfo, Any[], state, -1)
      e = h(e) 
      e = typed_expr(e.typ, :lambda, Any[params, varinfo, e.args[3]])
      state = state.parent
    elseif e.head == :body
      h(e)
      body = state.body
      state.body = Any[]
      e = typed_expr(e.typ, e.head, body)
    else
      e = h(e)
      if e.head == :call 
        for i = 1:length(e.args)
          x = e.args[i]
          if isa(x, Expr) # && x.typ != Any
            v = newlocal(state, x.typ)
            emit(state, typed_expr(x.typ, :(=), Any[v, x]))
            e.args[i] = v
          end
        end
      end
      if state.level == 0
        emit(state, e)
      end
    end
    state.level = state.level - 1
    if state.level == 0
      emit(state, e)
    end
    return e
  end
  function process(h, e::Any)
    if state.level == 0
      emit(state, e)
    end
    return h(e)
  end
  traverse(process, e)
end

"""
Substitute variables according to the given dictionary. We make no 
assumption of the replacement variable, which could clash with variables 
in inner lambdas. When clash happens, we rename the inner lambda first
before the substitution.
"""
function substSymbols(e, dict::Dict{Symbol,Symbol})
  function process(h, e::Expr)
    if e.head == :lambda
      params = getSymbols(e.args[1])
      varinfo = e.args[2]
      locals = getSymbols(varinfo[1])
      escapes = getSymbols(varinfo[2])
      new_dict = Dict{Symbol,Symbol}()
      for (k,v) in dict
        # only keep the keys for 
        if in(k, escapes)
          new_dict[k] = v
        end
      end
      # check for name clash
      clash_dict = Dict{Symbol,Symbol}()
      for (k,v) in new_dict
        if in(v, params) || in(v, locals)
          clash_dict[v] = gensym(string(v))
        end
      end
      old_dict = dict
      dict = clash_dict; e = h(e)
      dict = new_dict; e = h(e)
      dict = old_dict
    else
      e = h(e)
    end
    return e
  end
  process(h, e::Symbol) = get(dict, e, e)
  process(h, e::Slot) = haskey(dict, e.id) ? Slot(dict[e.id], e.typ) : e
  process(h, e::NewvarNode) = haskey(dict, e.name) ? NewvarNode(dict[e.name]) : e
  process(h, e::Any) = h(e)
  traverse(process, e)
end

end

