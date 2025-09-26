-- <vc-preamble>
def List.combinations (ls : List α) (k : Nat) : List (List α) :=
  sorry

abbrev List.sum (ls : List Int) : Int :=
  ls.foldl (· + ·) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def choose_best_sum (t : Int) (k : Nat) (ls : List Int) : Option Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_not_exceeds_target 
  (t : Int) (k : Nat) (ls : List Int)
  (h1 : t ≥ 1) (h2 : k ≥ 1) (h3 : !ls.isEmpty)
  (h4 : ∀ x ∈ ls, x ≥ 1 ∧ x ≤ 100) :
  (choose_best_sum t k ls).all (· ≤ t) :=
sorry

theorem none_if_k_too_large
  (t : Int) (k : Nat) (ls : List Int)
  (h1 : t ≥ 1)
  (h2 : k > ls.length)
  (h3 : ∀ x ∈ ls, x ≥ 1) :
  choose_best_sum t k ls = none :=
sorry

theorem result_is_sum_of_k_numbers
  (t : Int) (k : Nat) (ls : List Int)
  (h1 : t ≥ 1) (h2 : k ≥ 1)
  (h3 : ls.length ≥ 5)
  (h4 : ∀ x ∈ ls, x ≥ 1 ∧ x ≤ 100)
  (h5 : (choose_best_sum t k ls).isSome) :
  ∃ subset : List Int,
    subset ∈ ls.combinations k ∧ 
    subset.sum = Option.get! (choose_best_sum t k ls) :=
sorry

theorem edge_cases :
  choose_best_sum 100 3 [] = none ∧
  choose_best_sum (-1) 3 [1,2,3] = none ∧ 
  choose_best_sum 100 0 [1,2,3] = none :=
sorry

/-
info: 163
-/
-- #guard_msgs in
-- #eval choose_best_sum 163 3 [50, 55, 56, 57, 58]

/-
info: None
-/
-- #guard_msgs in
-- #eval choose_best_sum 163 3 [50]

/-
info: 228
-/
-- #guard_msgs in
-- #eval choose_best_sum 230 3 [91, 74, 73, 85, 73, 81, 87]
-- </vc-theorems>