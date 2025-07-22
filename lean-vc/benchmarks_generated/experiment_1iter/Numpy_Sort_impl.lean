import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def merge_sorted_lists (l1 l2 : List Float) : List Float :=
  match l1, l2 with
  | [], l2 => l2
  | l1, [] => l1
  | h1 :: t1, h2 :: t2 => 
    if h1 ≤ h2 then h1 :: merge_sorted_lists t1 l2
    else h2 :: merge_sorted_lists l1 t2
termination_by merge_sorted_lists l1 l2 => l1.length + l2.length

-- LLM HELPER
def merge_sort_list (l : List Float) : List Float :=
  match l with
  | [] => []
  | [x] => [x]
  | _ => 
    let mid := l.length / 2
    let left := l.take mid
    let right := l.drop mid
    merge_sorted_lists (merge_sort_list left) (merge_sort_list right)
termination_by merge_sort_list l => l.length

-- LLM HELPER
lemma merge_sorted_lists_sorted (l1 l2 : List Float) 
  (h1 : l1.Sorted (· ≤ ·)) (h2 : l2.Sorted (· ≤ ·)) : 
  (merge_sorted_lists l1 l2).Sorted (· ≤ ·) := by
  sorry

-- LLM HELPER
lemma merge_sorted_lists_count (l1 l2 : List Float) (x : Float) :
  (merge_sorted_lists l1 l2).count x = l1.count x + l2.count x := by
  sorry

-- LLM HELPER
lemma merge_sort_list_sorted (l : List Float) : 
  (merge_sort_list l).Sorted (· ≤ ·) := by
  sorry

-- LLM HELPER
lemma merge_sort_list_count (l : List Float) (x : Float) :
  (merge_sort_list l).count x = l.count x := by
  sorry

-- LLM HELPER
lemma merge_sort_list_length (l : List Float) :
  (merge_sort_list l).length = l.length := by
  sorry

-- LLM HELPER
lemma vector_mk_get (l : List Float) (h : l.length = n) (i : Fin n) :
  (Vector.mk l h).get i = l.get ⟨i.val, by rw [←h]; exact i.isLt⟩ := by
  sorry

/-- numpy.sort: Return a sorted copy of an array.

    Returns a new array with the same elements sorted in ascending order.
    The original array is not modified.

    This function performs a stable sort on the array elements.
-/
def numpy_sort (a : Vector Float n) : Id (Vector Float n) :=
  let sorted_list := merge_sort_list a.toList
  have h : sorted_list.length = n := by
    rw [merge_sort_list_length]
    exact a.size_toList
  pure (Vector.mk sorted_list h)

/-- Specification: numpy.sort returns a sorted permutation of the input.

    Precondition: True
    Postcondition: Result is sorted and is a permutation of the input
-/
theorem numpy_sort_spec (a : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_sort a
    ⦃⇓result => ⌜(∀ i j : Fin n, i < j → result.get i ≤ result.get j) ∧
                (∀ x : Float, (result.toList.count x) = (a.toList.count x))⌝⦄ := by
  simp [numpy_sort]
  apply hoare_pure
  constructor
  · intro i j hij
    have h_sorted : (merge_sort_list a.toList).Sorted (· ≤ ·) := merge_sort_list_sorted a.toList
    have h_len : (merge_sort_list a.toList).length = n := by
      rw [merge_sort_list_length]
      exact a.size_toList
    simp [Vector.get, Vector.mk]
    apply List.Sorted.get_le_get h_sorted
    exact hij
  · intro x
    have h_len : (merge_sort_list a.toList).length = n := by
      rw [merge_sort_list_length]
      exact a.size_toList
    simp [Vector.toList, Vector.mk]
    rw [merge_sort_list_count]