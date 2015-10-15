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

module DebugMsg

export init

@doc """
When this module is first loaded, we check if PROSPECT_DEV_MODE is set in environment.
If it is not, then all debug messages will be surpressed.
"""
const PROSPECT_DEV_MODE=haskey(ENV, "PROSPECT_DEV_MODE")

@doc """
A module using DebugMsg must call DebugMsg.init(), which expands to several local definitions
that provide three functions: set_debug_level, dprint, dprintln.
"""
function init()
  m = current_module()
  Base.eval(m, :(DEBUG_LVL = 0))
  if PROSPECT_DEV_MODE
    Base.eval(m, :(function set_debug_level(l) global DEBUG_LVL = l end))
    Base.eval(m, :(function dprint(l, msg...) if l <= DEBUG_LVL print(msg...) end end))
    Base.eval(m, :(function dprintln(l, msg...) if l <= DEBUG_LVL println(msg...) end end))
  else
    Base.eval(m, :(function set_debug_level(l) end))
    Base.eval(m, :(function dprint(l, msg...) end))
    Base.eval(m, :(function dprintln(l, msg...) end))
  end   
end

end

