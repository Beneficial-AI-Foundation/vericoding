import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def List.removeDuplicates (l : List Float) : List Float :=
  l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

-- LLM HELPER
def List.merge (l1 l2 : List Float) : List Float :=
  let rec merge_aux (acc : List Float) (xs ys : List Float) : List Float :=
    match xs, ys with
    | [], ys => acc ++ ys
    | xs, [] => acc ++ xs
    | x::xs', y::ys' => 
      if x ≤ y then merge_aux (acc ++ [x]) xs' (y::ys')
      else merge_aux (acc ++ [y]) (x::xs') ys'
  merge_aux [] l1 l2

-- LLM HELPER
def List.mergeSort (l : List Float) : List Float :=
  match l with
  | [] => []
  | [x] => [x]
  | _ => 
    let mid := l.length / 2
    let left := l.take mid
    let right := l.drop mid
    List.merge (List.mergeSort left) (List.mergeSort right)

-- LLM HELPER
def computeSetXor (ar1 ar2 : List Float) : List Float :=
  let unique1 := ar1.removeDuplicates
  let unique2 := ar2.removeDuplicates
  let in_ar1_not_ar2 := unique1.filter (fun x => ¬unique2.contains x)
  let in_ar2_not_ar1 := unique2.filter (fun x => ¬unique1.contains x)
  let combined := in_ar1_not_ar2 ++ in_ar2_not_ar1
  combined.mergeSort

/-- numpy.setxor1d: Find the set exclusive-or of two arrays.

    Return the sorted, unique values that are in only one (not both) of the
    input arrays. This is equivalent to the symmetric difference of two sets.
    
    The result contains elements that appear in ar1 but not in ar2, or in ar2 
    but not in ar1, sorted in ascending order.
-/
def numpy_setxor1d {n m k : Nat} (ar1 : Vector Float n) (ar2 : Vector Float m) : Id (Vector Float k) :=
  let result_list := computeSetXor ar1.toList ar2.toList
  let result_vector := Vector.mk result_list (by simp)
  pure result_vector

-- LLM HELPER
lemma list_sorted_implies_vector_sorted {l : List Float} {k : Nat} (h_sorted : ∀ i j : Nat, i < j → i < l.length → j < l.length → l.get! i ≤ l.get! j) :
  let v := Vector.mk l (by simp)
  ∀ i j : Fin k, i < j → v.get i ≤ v.get j := by
  sorry

-- LLM HELPER  
lemma list_nodups_implies_vector_nodups {l : List Float} {k : Nat} (h_nodups : l.Nodup) :
  let v := Vector.mk l (by simp)
  ∀ i j : Fin k, i ≠ j → v.get i ≠ v.get j := by
  sorry

-- LLM HELPER
lemma computeSetXor_correct (ar1 ar2 : List Float) :
  let result := computeSetXor ar1 ar2
  (∀ i j : Nat, i < j → i < result.length → j < result.length → result.get! i ≤ result.get! j) ∧
  result.Nodup ∧
  (∀ x : Float, x ∈ result ↔ (x ∈ ar1 ∧ x ∉ ar2) ∨ (x ∈ ar2 ∧ x ∉ ar1)) := by
  sorry

/-- Specification: numpy.setxor1d returns the symmetric difference of two arrays.

    Precondition: True (no special preconditions)
    Postcondition: 
    1. The result contains only elements that appear in exactly one of the input arrays
    2. The result is sorted in ascending order
    3. The result contains no duplicates
    4. Every element in the result comes from either ar1 or ar2 (but not both)
-/
theorem numpy_setxor1d_spec {n m k : Nat} (ar1 : Vector Float n) (ar2 : Vector Float m) :
    ⦃⌜True⌝⦄
    numpy_setxor1d ar1 ar2
    ⦃⇓result => ⌜
      -- Result is sorted
      (∀ i j : Fin k, i < j → result.get i ≤ result.get j) ∧
      -- Result has no duplicates
      (∀ i j : Fin k, i ≠ j → result.get i ≠ result.get j) ∧
      -- Every element in result is from exactly one input array
      (∀ i : Fin k, 
        (∃ j : Fin n, ar1.get j = result.get i ∧ ¬∃ l : Fin m, ar2.get l = result.get i) ∨
        (∃ j : Fin m, ar2.get j = result.get i ∧ ¬∃ l : Fin n, ar1.get l = result.get i)) ∧
      -- Every element that appears in exactly one input array is in the result
      (∀ x : Float, 
        ((∃ i : Fin n, ar1.get i = x ∧ ¬∃ j : Fin m, ar2.get j = x) ∨
         (∃ i : Fin m, ar2.get i = x ∧ ¬∃ j : Fin n, ar1.get j = x)) →
        ∃ i : Fin k, result.get i = x)
    ⌝⦄ := by
  intro h_pre
  simp [numpy_setxor1d]
  have h_correct := computeSetXor_correct ar1.toList ar2.toList
  constructor
  · apply list_sorted_implies_vector_sorted h_correct.1
  constructor
  · apply list_nodups_implies_vector_nodups h_correct.2.1
  constructor
  · intro i
    have h_mem := h_correct.2.2
    simp at h_mem
    sorry
  · intro x h_unique
    have h_mem := h_correct.2.2
    simp at h_mem
    sorry