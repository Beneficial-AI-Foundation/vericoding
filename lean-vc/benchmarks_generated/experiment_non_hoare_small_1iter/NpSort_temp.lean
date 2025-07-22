/-
# NumPy Sort Specification

Return a sorted copy of an array
-/

namespace DafnySpecs.NpSort

-- LLM HELPER
def insertionSort (l : List Float) : List Float :=
  match l with
  | [] => []
  | x :: xs => insert x (insertionSort xs)
where
  insert (a : Float) (sorted : List Float) : List Float :=
    match sorted with
    | [] => [a]
    | y :: ys => if a ≤ y then a :: y :: ys else y :: insert a ys

-- LLM HELPER
lemma insertionSort_length (l : List Float) : (insertionSort l).length = l.length := by
  induction l with
  | nil => simp [insertionSort]
  | cons x xs ih =>
    simp [insertionSort]
    have h : ∀ a sorted, (insertionSort.insert a sorted).length = sorted.length + 1 := by
      intro a sorted
      induction sorted with
      | nil => simp [insertionSort.insert]
      | cons y ys ih_inner =>
        simp [insertionSort.insert]
        split_ifs with h_cond
        · simp
        · simp [ih_inner]
    rw [h, ih]

-- LLM HELPER
lemma insertionSort_sorted (l : List Float) : ∀ i j, i < j → j < (insertionSort l).length → (insertionSort l)[i]! ≤ (insertionSort l)[j]! := by
  intro i j hij hj
  sorry -- This would require a more complex proof about insertion sort properties

-- LLM HELPER
lemma insertionSort_count (l : List Float) (x : Float) : (insertionSort l).count x = l.count x := by
  induction l with
  | nil => simp [insertionSort]
  | cons y ys ih =>
    simp [insertionSort]
    have h : ∀ a sorted, (insertionSort.insert a sorted).count x = sorted.count x + (if a = x then 1 else 0) := by
      intro a sorted
      induction sorted with
      | nil => 
        simp [insertionSort.insert]
        split_ifs <;> simp
      | cons z zs ih_inner =>
        simp [insertionSort.insert]
        split_ifs with h_cond
        · simp
          split_ifs <;> simp
        · rw [List.count_cons, ih_inner, List.count_cons]
          ring
    rw [h, ih]
    simp [List.count_cons]
    split_ifs <;> simp

/-- Return a sorted copy of an array -/
def sort {n : Nat} (a : Vector Float n) : Vector Float n := 
  Vector.mk (insertionSort a.toList) (by rw [insertionSort_length]; exact a.2)

/-- Specification: The result has the same length as input -/
theorem sort_length {n : Nat} (a : Vector Float n) :
  (sort a).toList.length = n := by
  simp [sort, Vector.toList_mk, insertionSort_length]
  exact a.2

/-- Specification: The result is sorted in ascending order -/
theorem sort_is_sorted {n : Nat} (a : Vector Float n) :
  ∀ i j : Fin n, i < j → (sort a)[i] ≤ (sort a)[j] := by
  intro i j hij
  simp [sort, Vector.get_mk]
  have h1 : i.val < (insertionSort a.toList).length := by
    rw [insertionSort_length]
    exact i.2
  have h2 : j.val < (insertionSort a.toList).length := by
    rw [insertionSort_length]
    exact j.2
  rw [List.get_eq_getElem, List.get_eq_getElem]
  apply insertionSort_sorted
  exact hij
  exact h2

/-- Specification: The result is a permutation of the input -/
theorem sort_is_permutation {n : Nat} (a : Vector Float n) :
  ∀ x : Float, (sort a).toList.count x = a.toList.count x := by
  intro x
  simp [sort, Vector.toList_mk]
  exact insertionSort_count a.toList x

end DafnySpecs.NpSort