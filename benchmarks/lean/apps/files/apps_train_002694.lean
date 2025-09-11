-- <vc-preamble>
def countOccurrences (arr : List Nat) (x : Nat) : Nat :=
  (arr.filter (· == x)).length

def getMode (arr : List Nat) : Nat :=
  match arr with
  | [] => 0
  | x::xs => (arr.foldl 
    (fun acc y => if countOccurrences arr y > countOccurrences arr acc then y else acc) 
    x)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def arrayEqualization (arr : List Nat) (k : Nat) : Nat := sorry

theorem equals_one_theorem (arr : List Nat) (h1 : arr.length > 0)
    (h2 : ∀ x ∈ arr, x ≥ 1 ∧ x ≤ 3) : 
  arrayEqualization arr 1 = (arr.filter (· ≠ getMode arr)).length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem identical_elements_theorem (arr : List Nat) (k : Nat)
    (h1 : arr.length > 0)
    (h2 : k ≥ 1)
    (h3 : k ≤ 10)
    (h4 : ∀ x ∈ arr, x = 1) :
  arrayEqualization arr k = 0 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval array_equalization [1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 1, 1] 2

/-
info: 2
-/
-- #guard_msgs in
-- #eval array_equalization [5, 2, 3, 5, 2, 2, 3, 5, 1, 2, 5, 1, 2, 5, 3] 7

/-
info: 1
-/
-- #guard_msgs in
-- #eval array_equalization [1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1] 9
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded