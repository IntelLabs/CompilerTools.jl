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

import CompilerTools.AstWalker
export constant_fold

binops = Set([:+; :-; :*; :/])

function constant_folder(node, symbol_table, top_level_number, is_top_level, read)
  if isa(node, Expr)
    if node.head == :(=)
      rhs = AstWalker.AstWalk(node.args[2], constant_folder, symbol_table)
      if isa(rhs, Number)
        symbol_table[node.args[1]] = rhs
      end
      return node
    elseif node.head == :call
      if in(node.args[1], binops) && length(node.args)==3
	      node.args[2] = AstWalker.AstWalk(node.args[2], constant_folder, symbol_table)[1]
	      node.args[3] = AstWalker.AstWalk(node.args[3], constant_folder, symbol_table)[1]
        if isa(node.args[2], Number) && isa(node.args[3], Number)
          return eval(node)
        end
      end
    end
  elseif isa(node, Symbol)
    if haskey(symbol_table, node)
      return symbol_table[node]
    end
  elseif isa(node, Number)
    return node
  end
  return CompilerTools.AstWalker.ASTWALK_RECURSE
end

function constant_fold(fn)
	symbol_table = Dict{Symbol, Number}()
	fn = AstWalker.AstWalk(fn, constant_folder, symbol_table)
	return fn
end

#=
macro constant_fold(fn)
	symbol_table = Dict{Symbol, Number}()
	AstWalker.AstWalk(fn, constant_folder, symbol_table)
  println(symbol_table)
  println(fn)
  return esc(fn)
end

@constant_fold function test(z)
  a = 3
  b = 4
  c = a - b
  d = z + c
  return d
end
=#
