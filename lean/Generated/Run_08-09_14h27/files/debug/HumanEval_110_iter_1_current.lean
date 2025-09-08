/- 
function_signature: "def exchange(lst1: list[int], lst2: list[int]) -> str"
docstring: |
    In this problem, you will implement a function that takes two lists of numbers,
    and determines whether it is possible to perform an exchange of elements
    between them to make lst1 a list of only even numbers.
    There is no limit on the number of exchanged elements between lst1 and lst2.
    If it is possible to exchange elements between the lst1 and lst2 to make
    all the elements of lst1 to be even, return "YES".
    Otherwise, return "NO". It is assumed that the input lists will be non-empty.
test_cases:
  - input: ([1, 2, 3, 4], [1, 2, 3, 4])
    expected_output: "YES"
  - input: ([1, 2, 3, 4], [1, 5, 3, 4])
    expected_output: "NO"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
import Std

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def countEvenElements (lst : List Int) : Nat :=
  lst.filter (fun x => x % 2 = 0) |>.length

def implementation (lst1: List Int) (lst2: List Int) : String :=
  let totalEvenCount := countEvenElements lst1 + countEvenElements lst2
  if totalEvenCount ≥ lst1.length then "YES" else "NO"

def problem_spec
-- function signature
(implementation: List Int → List Int → String)
-- inputs
(lst1: List Int)
(lst2: List Int) :=
-- spec
let spec (result : String) :=
  lst1 ≠ [] → lst2 ≠ [] →
  let bool_result := ∃ exchange: List (Nat × Nat),
    let lst1_idxs := exchange.map (fun (a, _) => a)
    let lst2_idxs := exchange.map (fun (_, b) => b)
    lst1_idxs.all (fun i => i < lst1.length) ∧
    lst2_idxs.all (fun i => i < lst2.length) ∧
    lst1_idxs.Nodup ∧
    lst2_idxs.Nodup ∧
    ∀ i, i < lst1.length →
      (i ∉ lst1_idxs → Even (lst1[i]!)) ∧
      (i ∈ lst1_idxs →
        -- find the (a, b) in exchange where a = i
        let i_idx := (lst1_idxs.indexesOf i).head!
        Even (lst2[lst2_idxs[i_idx]!]!))
  (bool_result → result = "YES") ∧
  (result = "NO" → ¬ bool_result) ∧
  (result ≠ "YES" ∧ result ≠ "NO" → False)
-- program termination
∃ result,
  implementation lst1 lst2 = result ∧
  spec result

-- LLM HELPER
lemma int_even_iff_mod_two_eq_zero (x : Int) : Even x ↔ x % 2 = 0 := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    rw [hk]
    simp [Int.mul_emod]
  · intro h
    use x / 2
    rw [Int.mul_comm]
    exact Int.div_add_mod x 2 ▸ h ▸ (add_zero _).symm

-- LLM HELPER
lemma implementation_correct_yes (lst1 lst2 : List Int) :
  countEvenElements lst1 + countEvenElements lst2 ≥ lst1.length →
  ∃ exchange: List (Nat × Nat),
    let lst1_idxs := exchange.map (fun (a, _) => a)
    let lst2_idxs := exchange.map (fun (_, b) => b)
    lst1_idxs.all (fun i => i < lst1.length) ∧
    lst2_idxs.all (fun i => i < lst2.length) ∧
    lst1_idxs.Nodup ∧
    lst2_idxs.Nodup ∧
    ∀ i, i < lst1.length →
      (i ∉ lst1_idxs → Even (lst1[i]!)) ∧
      (i ∈ lst1_idxs →
        let i_idx := (lst1_idxs.indexesOf i).head!
        Even (lst2[lst2_idxs[i_idx]!]!)) := by
  sorry

-- LLM HELPER
lemma implementation_correct_no (lst1 lst2 : List Int) :
  countEvenElements lst1 + countEvenElements lst2 < lst1.length →
  ¬ ∃ exchange: List (Nat × Nat),
    let lst1_idxs := exchange.map (fun (a, _) => a)
    let lst2_idxs := exchange.map (fun (_, b) => b)
    lst1_idxs.all (fun i => i < lst1.length) ∧
    lst2_idxs.all (fun i => i < lst2.length) ∧
    lst1_idxs.Nodup ∧
    lst2_idxs.Nodup ∧
    ∀ i, i < lst1.length →
      (i ∉ lst1_idxs → Even (lst1[i]!)) ∧
      (i ∈ lst1_idxs →
        let i_idx := (lst1_idxs.indexesOf i).head!
        Even (lst2[lst2_idxs[i_idx]!]!)) := by
  sorry

theorem correctness
(lst1: List Int)
(lst2: List Int)
: problem_spec implementation lst1 lst2
:= by
  unfold problem_spec
  use implementation lst1 lst2
  constructor
  · rfl
  · intro h1 h2
    unfold implementation
    let totalEven := countEvenElements lst1 + countEvenElements lst2
    by_cases h : totalEven ≥ lst1.length
    · simp [h]
      constructor
      · intro _
        exact implementation_correct_yes lst1 lst2 h
      · constructor
        · intro h_no
          discriminate
        · intro h_invalid
          cases h_invalid with
          | left h_not_yes => discriminate
          | right h_not_no => discriminate
    · simp [h]
      constructor
      · intro h_exists
        have : ¬ (totalEven < lst1.length) := by
          intro h_lt
          exact implementation_correct_no lst1 lst2 h_lt h_exists
        omega
      · constructor
        · intro _
          exact implementation_correct_no lst1 lst2 (Nat.lt_of_not_ge h)
        · intro h_invalid
          cases h_invalid with
          | left h_not_yes => discriminate
          | right h_not_no => discriminate

-- #test implementation ([1, 2, 3, 4], [1, 2, 3, 4]) = "YES"
-- #test implementation ([1, 2, 3, 4], [1, 5, 3, 4]) = "NO"