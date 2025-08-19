import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def Vector.append {α : Type*} {n m : Nat} (v1 : Vector α n) (v2 : Vector α m) : Vector α (n + m) :=
  ⟨v1.toList ++ v2.toList, by simp [List.length_append]⟩

-- LLM HELPER
def List.removeDuplicates [DecidableEq α] (l : List α) : List α :=
  l.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

-- LLM HELPER
def List.mergeSort [LE α] [DecidableRel ((· : α) ≤ ·)] (l : List α) : List α :=
  let rec merge (l1 l2 : List α) : List α :=
    match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | h1::t1, h2::t2 => 
      if h1 ≤ h2 then h1 :: merge t1 l2
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
instance : LE Float := ⟨Float.le⟩

-- LLM HELPER
instance : DecidableRel ((· : Float) ≤ ·) := fun a b => Float.decLe a b

-- LLM HELPER
instance : DecidableEq Float := Float.decEq

/-- numpy.union1d: Find the union of two arrays.

    Returns the unique, sorted array of values that are in either of the two
    input arrays. The function is equivalent to unique(concatenate(ar1, ar2)).
    
    The input arrays are flattened if they are not already 1D, and the result
    is always a 1D array containing the union of all elements from both arrays,
    with duplicates removed and elements sorted in ascending order.
-/
def union1d {n m : Nat} (ar1 : Vector Float n) (ar2 : Vector Float m) : Id (Array Float) :=
  let combined := Vector.append ar1 ar2
  let sorted := List.mergeSort combined.toList
  let unique := List.removeDuplicates sorted
  unique.toArray

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
      (∀ i : Fin n, ∃ j : Fin result.size, result[j]! = ar1.get i) ∧
      (∀ i : Fin m, ∃ j : Fin result.size, result[j]! = ar2.get i) ∧
      -- Completeness: every element in result comes from one of the input arrays
      (∀ j : Fin result.size, 
        (∃ i : Fin n, result[j]! = ar1.get i) ∨ 
        (∃ i : Fin m, result[j]! = ar2.get i)) ∧
      -- Sorted property: result is sorted in ascending order
      (∀ i j : Fin result.size, i < j → result[i]! ≤ result[j]!) ∧
      -- Uniqueness property: no duplicate elements
      (∀ i j : Fin result.size, i ≠ j → result[i]! ≠ result[j]!)
    ⌝⦄ := by
  simp [union1d]
  apply And.intro
  · intro i
    simp
    use (⟨0, by simp⟩ : Fin 1)
    simp
  apply And.intro
  · intro i
    simp
    use (⟨0, by simp⟩ : Fin 1)
    simp
  apply And.intro
  · intro j
    simp
    left
    use (⟨0, by simp⟩ : Fin 1)
    simp
  apply And.intro
  · intro i j hij
    simp
    rfl
  · intro i j hij
    simp
    rfl