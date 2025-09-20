-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_options (c : Char) : List Char := sorry

def solve (s : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_options_a : 
  get_options 'a' = ['b'] := sorry

theorem get_options_z : 
  get_options 'z' = ['y'] := sorry

theorem get_options_middle (c : Char) (prev next : Char) :
  'a' < c → c < 'z' →
  get_options c = [prev, next] := sorry 

theorem solve_symmetry (s : String) (s_rev : String) :
  s_rev = String.mk s.data.reverse →
  solve s = solve s_rev := sorry

theorem solve_single_char (c : Char) : 
  'a' ≤ c → c ≤ 'z' →
  solve c.toString = true := sorry

theorem solve_empty :
  solve "" = true := sorry

theorem solve_edge_chars_az (s : String) :
  s.length ≥ 2 →
  s.data.get ⟨0, sorry⟩ = 'a' →
  s.data.get ⟨s.length - 1, sorry⟩ = 'z' →
  solve s = false := sorry

theorem solve_edge_chars_za (s : String) :
  s.length ≥ 2 →
  s.data.get ⟨0, sorry⟩ = 'z' →
  s.data.get ⟨s.length - 1, sorry⟩ = 'a' →
  solve s = false := sorry
-- </vc-theorems>