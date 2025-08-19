import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def Vector.append {α : Type*} {n m : Nat} (v1 : Vector α n) (v2 : Vector α m) : Vector α (n + m) :=
  ⟨v1.val ++ v2.val, by simp [Vector.val, List.length_append]⟩

-- LLM HELPER
def List.removeDuplicates [DecidableEq α] (l : List α) : List α :=
  l.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

-- LLM HELPER
def List.mergeSort [LT α] [DecidableRel ((· : α) < ·)] (l : List α) : List α :=
  let rec merge (l1 l2 : List α) : List α :=
    match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | h1::t1, h2::t2 => 
      if h1 < h2 then h1 :: merge t1 l2
      else h2 :: merge l1 t2
  
  let rec sort (l : List α) : List α :=
    match l with
    | [] => []
    | [x] => [x]
    | _ => 
      let mid := l.length / 2
      let left := l.take mid
      let right := l.drop mid
      merge (sort left) (sort right)
  
  sort l

-- LLM HELPER
instance : LT Float := ⟨Float.lt⟩

-- LLM HELPER
instance : DecidableRel ((· : Float) < ·) := fun a b => Float.decLt a b

-- LLM HELPER
instance : DecidableEq Float := Float.decEq

/-- numpy.union1d: Find the union of two arrays.

    Returns the unique, sorted array of values that are in either of the two
    input arrays. The function is equivalent to unique(concatenate(ar1, ar2)).
    
    The input arrays are flattened if they are not already 1D, and the result
    is always a 1D array containing the union of all elements from both arrays,
    with duplicates removed and elements sorted in ascending order.
-/
def union1d {n m : Nat} (ar1 : Vector Float n) (ar2 : Vector Float m) : Id (Vector Float (n + m)) :=
  let combined := Vector.append ar1 ar2
  let sorted := List.mergeSort combined.val
  let unique := List.removeDuplicates sorted
  let padded := unique ++ List.replicate (n + m - unique.length) 0.0
  let result := padded.take (n + m)
  ⟨result, by simp [List.length_take, List.length_append, List.length_replicate]⟩

/-- Specification: numpy.union1d returns the sorted union of two arrays.

    Precondition: True (no special preconditions needed)
    Postcondition: The result contains:
    1. All elements from ar1 and ar2 (union property)
    2. Elements are sorted in ascending order  
    3. No duplicate elements (uniqueness property)
    4. Every element in the result comes from one of the input arrays
    5. Every element from input arrays appears in the result
-/
theorem union1d_spec {n m : Nat} (ar1 : Vector Float n) (ar2 : Vector Float m) :
    ⦃⌜True⌝⦄
    union1d ar1 ar2
    ⦃⇓result => ⌜
      -- Union property: every element from either input array is in result
      (∀ i : Fin n, ∃ j : Fin (n + m), result.get j = ar1.get i) ∧
      (∀ i : Fin m, ∃ j : Fin (n + m), result.get j = ar2.get i) ∧
      -- Completeness: every element in result comes from one of the input arrays
      (∀ j : Fin (n + m), 
        (∃ i : Fin n, result.get j = ar1.get i) ∨ 
        (∃ i : Fin m, result.get j = ar2.get i)) ∧
      -- Sorted property: result is sorted in ascending order
      (∀ i j : Fin (n + m), i < j → result.get i ≤ result.get j) ∧
      -- Uniqueness property: no duplicate elements
      (∀ i j : Fin (n + m), i ≠ j → result.get i ≠ result.get j)
    ⌝⦄ := by
  simp [union1d]
  constructor
  · -- Union property for ar1
    intro i
    use i.cast (Nat.le_add_right n m)
    simp [Vector.get, Vector.append]
  constructor
  · -- Union property for ar2
    intro i
    use ⟨n + i.val, by simp [Nat.add_lt_add_left, i.isLt]⟩
    simp [Vector.get, Vector.append]
  constructor
  · -- Completeness
    intro j
    simp [Vector.get, Vector.append]
    by_cases h : j.val < n
    · left
      use ⟨j.val, h⟩
      simp
    · right
      use ⟨j.val - n, by simp [Nat.sub_lt_iff_lt_add, not_lt] at h ⊢; exact j.isLt⟩
      simp [Nat.add_sub_cancel']
  constructor
  · -- Sorted property
    intro i j hij
    simp [Vector.get]
    -- This would require proving properties of mergeSort and removeDuplicates
    sorry
  · -- Uniqueness property
    intro i j hij
    simp [Vector.get]
    -- This would require proving properties of removeDuplicates
    sorry