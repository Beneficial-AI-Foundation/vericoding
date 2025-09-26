-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Funnel := List (List Char)

def funnel_out (f : Funnel) : List Char := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem funnel_structure_preserved (f : Funnel) :
  let f' := f
  f = f' := sorry

theorem all_letters_output (f : Funnel) :
  let input_letters := f.join
  List.length (funnel_out f) = List.length input_letters := sorry

theorem funnel_fills_bottom (f : Funnel) :
  let total_letters := f.join.length 
  (funnel_out f).length = total_letters := sorry

theorem simple_cases :
  funnel_out [['a']] = ['a'] ∧  
  funnel_out [['a', 'b'], ['c']] = ['c', 'a', 'b'] := sorry

/-
info: 'q'
-/
-- #guard_msgs in
-- #eval funnel_out [["q"]]

/-
info: 'abc'
-/
-- #guard_msgs in
-- #eval funnel_out [["b", "c"], ["a"]]

/-
info: 'fbadec'
-/
-- #guard_msgs in
-- #eval funnel_out [["d", "a", "c"], ["b", "e"], ["f"]]
-- </vc-theorems>