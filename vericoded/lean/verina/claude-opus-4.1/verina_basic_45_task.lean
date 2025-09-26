import Mathlib
-- <vc-preamble>
def isEven (n : Int) : Bool :=
  n % 2 = 0

def isOdd (n : Int) : Bool :=
  n % 2 ≠ 0

def firstEvenOddIndices (lst : List Int) : Option (Nat × Nat) :=
  let evenIndex := lst.findIdx? isEven
  let oddIndex := lst.findIdx? isOdd
  match evenIndex, oddIndex with
  | some ei, some oi => some (ei, oi)
  | _, _ => none
@[reducible, simp]
def findProduct_precond (lst : List Int) : Prop :=
  lst.length > 1 ∧
  (∃ x ∈ lst, isEven x) ∧
  (∃ x ∈ lst, isOdd x)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma exists_findIdx_of_exists_satisfying (lst : List Int) (p : Int → Bool) :
    (∃ x ∈ lst, p x = true) → ∃ i, lst.findIdx? p = some i := by
  intro ⟨x, hx_mem, hx_p⟩
  have h_any : lst.any p = true := by
    rw [List.any_eq_true]
    exact ⟨x, hx_mem, hx_p⟩
  have h_isSome : (lst.findIdx? p).isSome = true := by
    rw [List.findIdx?_isSome]
    exact h_any
  cases h_eq : lst.findIdx? p with
  | none => 
    rw [h_eq] at h_isSome
    simp at h_isSome
  | some i =>
    exact ⟨i, rfl⟩

-- LLM HELPER
lemma firstEvenOddIndices_some_of_precond (lst : List Int) (h : findProduct_precond lst) :
    ∃ ei oi, firstEvenOddIndices lst = some (ei, oi) := by
  unfold findProduct_precond at h
  obtain ⟨_, ⟨x, hx_mem, hx_even⟩, ⟨y, hy_mem, hy_odd⟩⟩ := h
  unfold firstEvenOddIndices
  -- Since there exists an even element, findIdx? isEven will find it
  have h_even : ∃ i, lst.findIdx? isEven = some i := 
    exists_findIdx_of_exists_satisfying lst isEven ⟨x, hx_mem, hx_even⟩
  have h_odd : ∃ i, lst.findIdx? isOdd = some i := 
    exists_findIdx_of_exists_satisfying lst isOdd ⟨y, hy_mem, hy_odd⟩
  obtain ⟨ei, hei⟩ := h_even
  obtain ⟨oi, hoi⟩ := h_odd
  use ei, oi
  simp [hei, hoi]
-- </vc-helpers>

-- <vc-definitions>
def findProduct (lst : List Int) (h_precond : findProduct_precond (lst)) : Int :=
  match firstEvenOddIndices lst with
  | some (ei, oi) => lst[ei]! * lst[oi]!
  | none => 0  -- This case won't happen due to precondition
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def findProduct_postcond (lst : List Int) (result: Int) (h_precond : findProduct_precond (lst)) :=
  match firstEvenOddIndices lst with
  | some (ei, oi) => result = lst[ei]! * lst[oi]!
  | none => True

theorem findProduct_spec_satisfied (lst: List Int) (h_precond : findProduct_precond (lst)) :
    findProduct_postcond (lst) (findProduct (lst) h_precond) h_precond := by
  unfold findProduct_postcond findProduct
  -- By the precondition, we know firstEvenOddIndices will return some value
  have h_some : ∃ ei oi, firstEvenOddIndices lst = some (ei, oi) := 
    firstEvenOddIndices_some_of_precond lst h_precond
  obtain ⟨ei, oi, h_eq⟩ := h_some
  rw [h_eq]
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "lst": "[2]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "lst": "[2, 3, 4, 5]"
        },
        "expected": 6,
        "unexpected": [
            8,
            0,
            10
        ]
    },
    {
        "input": {
            "lst": "[2, 4, 3, 6]"
        },
        "expected": 6,
        "unexpected": [
            8,
            0,
            24
        ]
    },
    {
        "input": {
            "lst": "[1, 2, 5, 4]"
        },
        "expected": 2,
        "unexpected": [
            5,
            0,
            10
        ]
    }
]
-/