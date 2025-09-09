-- <vc-helpers>
-- </vc-helpers>

def find_permutations (arr : List Int) : List (Nat × Nat) :=
  sorry

theorem permutations_results_valid (arr : List Int) 
  (h : ∀ x ∈ arr, x > 0) : 
  let result := find_permutations arr
  ∀ pair ∈ result,
    (∃ a b : Nat, pair = (a,b)) ∧ 
    (pair.1 > 0 ∧ pair.2 > 0) ∧
    pair.1 + pair.2 = arr.length :=
  sorry

theorem permutations_unique (arr : List Int)
  (h : ∀ x ∈ arr, x > 0) :
  let result := find_permutations arr 
  List.Nodup result :=
  sorry

theorem preserves_input (arr : List Int) :
  let orig := arr
  let _ := find_permutations arr
  arr = orig :=
  sorry

theorem valid_splits {arr : List Int}
  (h1 : ∀ x ∈ arr, 0 < x ∧ x ≤ 5) :
  let result := find_permutations arr
  ∀ pair ∈ result,
    let left := (arr.take pair.1)
    let right := (arr.drop pair.1)
    (∀ x ∈ left, 1 ≤ x ∧ x ≤ pair.1) ∧
    (List.Nodup left) ∧
    (List.Nodup right) ∧
    (∀ x ∈ right, 1 ≤ x ∧ x ≤ pair.2) :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval len find_permutations(test1)

/-
info: 1
-/
-- #guard_msgs in
-- #eval len find_permutations(test2)

/-
info: 0
-/
-- #guard_msgs in
-- #eval len find_permutations(test3)

-- Apps difficulty: interview
-- Assurance level: unguarded