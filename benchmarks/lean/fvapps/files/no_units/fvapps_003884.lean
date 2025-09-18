-- <vc-preamble>
def String.count (s : String) (c : Char) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def added_char (base modified : String) : Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem added_char_correct (base : String) (c : Char) :
  let modified := base ++ String.mk (List.replicate 3 c)
  added_char base modified = c :=
sorry

theorem length_difference (base : String) (c : Char) :
  let modified := base ++ String.mk (List.replicate 3 c)
  modified.length = base.length + 3 :=
sorry
-- </vc-theorems>