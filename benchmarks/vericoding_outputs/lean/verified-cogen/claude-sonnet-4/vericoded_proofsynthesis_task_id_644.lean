import Mathlib
-- <vc-preamble>
@[reducible, simp]
def reverseToK_precond (list : Array Int) (n : Nat) : Prop :=
  list.size > 0 ∧ 0 < n ∧ n < list.size
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def Array.reverse_slice (arr : Array α) (start finish : Nat) : Array α :=
  let slice := arr.extract start finish
  let reversed := slice.reverse
  let before := arr.extract 0 start
  let after := arr.extract finish arr.size
  before ++ reversed ++ after

-- LLM HELPER
lemma Array.extract_zero_eq_take (arr : Array α) (n : Nat) (h : n ≤ arr.size) :
  (arr.extract 0 n).toList = List.take n arr.toList := by
  rw [Array.toList_extract]
  simp [List.extract, min_eq_left h]

-- LLM HELPER
lemma Array.extract_n_to_size_eq_drop (arr : Array α) (n : Nat) (h : n ≤ arr.size) :
  (arr.extract n arr.size).toList = List.drop n arr.toList := by
  rw [Array.toList_extract]
  simp [List.extract]
-- </vc-helpers>

-- <vc-definitions>
def reverseToK (list : Array Int) (n : Nat) (h_precond : reverseToK_precond list n) : Array Int :=
  let slice := list.extract 0 n
  let reversed := slice.reverse
  let remaining := list.extract n list.size
  reversed ++ remaining
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def reverseToK_postcond (list : Array Int) (n : Nat) (result : Array Int) (h_precond : reverseToK_precond list n) : Prop :=
  result.toList = (list.toList.take n).reverse ++ (list.toList.drop n)

theorem reverseToK_spec_satisfied (list : Array Int) (n : Nat) (h_precond : reverseToK_precond list n) :
    reverseToK_postcond list n (reverseToK list n h_precond) h_precond := by
  unfold reverseToK reverseToK_postcond
  simp only [Array.toList_append, Array.toList_reverse]
  have h1 : n ≤ list.size := by
    obtain ⟨h_size, h_pos_n, h_n_lt⟩ := h_precond
    exact Nat.le_of_lt h_n_lt
  rw [Array.extract_zero_eq_take list n h1]
  rw [Array.extract_n_to_size_eq_drop list n h1]
-- </vc-theorems>

def main : IO Unit := 
  return ()