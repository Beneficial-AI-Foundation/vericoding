import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- FindEvenNumbers: Extract all even numbers from an array.

    Given an array of integers, returns a new array containing only the even numbers
    from the input array, preserving their relative order.

    The specification ensures:
    - All even numbers from the input are included in the result
    - No numbers not in the input appear in the result  
    - All numbers in the result are even
    - The relative order of even numbers is preserved
-/
def findEvenNumbers (arr : Array Int) : Id (Array Int) :=
  arr.filter (fun x => x % 2 = 0)

-- LLM HELPER
lemma array_filter_mem_of_mem_and_prop (arr : Array α) (p : α → Bool) (x : α) :
  x ∈ arr.toList ∧ p x = true → x ∈ (arr.filter p).toList := by
  intro h
  rw [Array.mem_toList, Array.filter_toList]
  exact List.mem_filter.mpr h

-- LLM HELPER
lemma array_filter_not_mem_if_not_in_orig (arr : Array α) (p : α → Bool) (x : α) :
  x ∉ arr.toList → x ∉ (arr.filter p).toList := by
  intro h
  rw [Array.mem_toList, Array.filter_toList]
  intro contra
  have : x ∈ arr.toList := by
    rw [← Array.mem_toList]
    exact List.mem_of_mem_filter contra
  contradiction

-- LLM HELPER
lemma array_filter_all_satisfy_prop (arr : Array α) (p : α → Bool) (i : Fin (arr.filter p).size) :
  p ((arr.filter p)[i]) = true := by
  have h := Array.getElem_filter arr p i.val i.isLt
  obtain ⟨j, hj₁, hj₂, hj₃⟩ := h
  rw [← hj₃]
  exact hj₂

-- LLM HELPER
lemma array_filter_preserves_order (arr : Array α) (p : α → Bool) (i j : Fin (arr.filter p).size) :
  i < j → ∃ n m : Fin arr.size, n < m ∧ (arr.filter p)[i] = arr[n] ∧ (arr.filter p)[j] = arr[m] := by
  intro hij
  have hi := Array.getElem_filter arr p i.val i.isLt
  have hj := Array.getElem_filter arr p j.val j.isLt
  obtain ⟨ni, hni₁, hni₂, hni₃⟩ := hi
  obtain ⟨nj, hnj₁, hnj₂, hnj₃⟩ := hj
  use ⟨ni, hni₁⟩, ⟨nj, hnj₁⟩
  constructor
  · have : i.val < j.val := hij
    have filter_indices_increasing : ni < nj := by
      apply Array.filter_indices_increasing
      exact this
    exact filter_indices_increasing
  constructor
  · exact hni₃
  · exact hnj₃

/-- Specification: findEvenNumbers returns an array containing exactly the even numbers
    from the input array in their original order.

    Precondition: True (no special preconditions)
    Postcondition:
    - Every even number in arr appears in the result
    - Every number not in arr does not appear in the result
    - Every number in the result is even
    - The relative order of even numbers is preserved
-/
theorem findEvenNumbers_spec (arr : Array Int) :
    ⦃⌜True⌝⦄
    findEvenNumbers arr
    ⦃⇓result => ⌜(∀ x : Int, x ∈ arr.toList ∧ x % 2 = 0 → x ∈ result.toList) ∧
                 (∀ x : Int, x ∉ arr.toList → x ∉ result.toList) ∧
                 (∀ i : Fin result.size, result[i] % 2 = 0) ∧
                 (∀ i j : Fin result.size, i < j → 
                   ∃ n m : Fin arr.size, n < m ∧ result[i] = arr[n] ∧ result[j] = arr[m])⌝⦄ := by
  mvcgen [findEvenNumbers]
  constructor
  constructor
  constructor
  · intro x h
    apply array_filter_mem_of_mem_and_prop
    exact h
  constructor
  · intro x h
    apply array_filter_not_mem_if_not_in_orig
    exact h
  constructor
  · intro i
    have : (fun x => x % 2 = 0) ((arr.filter (fun x => x % 2 = 0))[i]) = true := by
      apply array_filter_all_satisfy_prop
    simp at this
    exact this
  · intro i j hij
    apply array_filter_preserves_order
    exact hij