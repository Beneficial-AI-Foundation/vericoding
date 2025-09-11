-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_lcs_strings (n m : Nat) (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_bounds 
  (n m : Nat) (s : String)
  (hn : n > 0) (hm : m ≥ 2)
  (hs : String.length s = n) :
  let result := calculate_lcs_strings n m s
  0 ≤ result ∧ result ≤ n * n * (m-1) :=
sorry

theorem decreasing_m_property
  (n m : Nat) (s : String)
  (hn : n > 0) (hm : m > 2)
  (hs : String.length s = n) :
  let result1 := calculate_lcs_strings n m s
  let result2 := calculate_lcs_strings n (m-1) s
  result1 ≥ result2 :=
sorry

theorem alternating_strings_property
  (n m : Nat) (s : String)
  (hn : n > 1) (hm : m ≥ 2)
  (hs : s = String.mk (List.map (fun i => if i % 2 = 0 then 'a' else 'b') (List.range n))) :
  calculate_lcs_strings n m s > 0 :=
sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval calculate_lcs_strings 3 3 "aaa"

/-
info: 11
-/
-- #guard_msgs in
-- #eval calculate_lcs_strings 3 3 "aab"

/-
info: 789
-/
-- #guard_msgs in
-- #eval calculate_lcs_strings 10 9 "abacadefgh"
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded