-- <vc-preamble>
def uniq_c {α : Type u} (xs : List α) : List (α × Nat) :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | h :: t => h + sum t
-- </vc-definitions>

-- <vc-theorems>
theorem uniq_c_length_invariants {α : Type u} (xs : List α) :
  let result := uniq_c xs
  (∀ p ∈ result, (Prod.snd p) > 0) ∧ 
  sum (result.map Prod.snd) = xs.length :=
sorry

theorem uniq_c_groups_consecutive {α : Type u} [BEq α] (xs : List α) :
  let result := uniq_c xs
  let indices := List.range xs.length
  ∀ (i j : Nat), i < xs.length → j < xs.length →
    ∀ p ∈ result,
      (i < j) → 
      (j - i < Prod.snd p) →
      xs[i]? = some (Prod.fst p) →
      xs[j]? = some (Prod.fst p) :=
sorry

theorem uniq_c_single_element {α : Type u} [BEq α] (x : α) (n : Nat) :
  uniq_c (List.replicate n x) = [(x, n)] :=
sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval uniq_c ["a", "a", "b", "b", "c", "a", "b", "c"]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval uniq_c ["a", "a", "a", "b", "b", "b", "c", "c", "c"]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval uniq_c [None, "a", "a"]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded