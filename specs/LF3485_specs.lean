-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_bounds {s : String} (h : s.length > 0) :
  solve s ≥ 0 ∧ solve s ≤ (s.length * (s.length + 1)) / 2 :=
  sorry

theorem solve_expected {s : String} (h : s.length > 0) :
  solve s = s.data.enum.foldl (fun acc (i, c) => 
    if c.toNat % 2 = 1 then 
      acc + (i + 1)
    else acc) 0 :=
  sorry

theorem solve_even_only {s : String} (h : s.length > 0)
  (h_even : ∀ c ∈ s.data, c.toNat % 2 = 0) :
  solve s = 0 :=
  sorry

theorem solve_odd_only {s : String} (h : s.length > 0)
  (h_odd : ∀ c ∈ s.data, c.toNat % 2 = 1) :
  solve s = (s.length * (s.length + 1)) / 2 :=
  sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval solve "1341"

/-
info: 10
-/
-- #guard_msgs in
-- #eval solve "1357"

/-
info: 12
-/
-- #guard_msgs in
-- #eval solve "13471"
-- </vc-theorems>