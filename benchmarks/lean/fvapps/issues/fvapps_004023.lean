-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | (h::t) => h + sum t

def explode {α : Type} : List α → List (List α) := sorry

theorem explode_integers {arr : List Nat} 
  (h1 : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 10) 
  (h2 : 1 ≤ arr.length ∧ arr.length ≤ 5) :
  let result := explode arr
  (result.length = arr.sum) ∧ 
  (∀ x ∈ result, x = arr) := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def VoidResult := List (List String)
def VOID : VoidResult := []
-- </vc-definitions>

-- <vc-theorems>
theorem explode_strings (arr : List String)
  (h : 1 ≤ arr.length ∧ arr.length ≤ 5) 
  (h2 : ∀ s ∈ arr, s.length ≤ 5) :
  explode arr = VOID := sorry
-- </vc-theorems>