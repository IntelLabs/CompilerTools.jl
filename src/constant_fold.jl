import CompilerTools.AstWalker

binops = Set({:+, :-, :*, :/})

function constant_folder(node, symbol_table, top_level_number, is_top_level, read)
  if isa(node, Expr)
    if node.head == :(=)
	    rhs = AstWalker.AstWalk(node.args[2], constant_folder, symbol_table)
      if isa(rhs[1], Number)
        symbol_table[node.args[1]] = rhs[1]
      end
      return node
    elseif node.head == :call
      if in(node.args[1], binops)
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
  return nothing
end

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
