-- <vc-preamble>
def sum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | h :: t => h + sum t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def uniq_c {α : Type u} (xs : List α) : List (α × Nat) :=
  sorry
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
-- </vc-theorems>