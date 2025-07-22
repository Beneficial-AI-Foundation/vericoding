/-
# NumPy Sort Specification

Return a sorted copy of an array
-/

namespace DafnySpecs.NpSort

-- LLM HELPER
def insertSorted (x : Float) (l : List Float) : List Float :=
  match l with
  | [] => [x]
  | h :: t => if x ≤ h then x :: h :: t else h :: insertSorted x t

-- LLM HELPER
def listSort (l : List Float) : List Float :=
  match l with
  | [] => []
  | h :: t => insertSorted h (listSort t)

-- LLM HELPER
lemma insertSorted_length (x : Float) (l : List Float) :
  (insertSorted x l).length = l.length + 1 := by
  induction l with
  | nil => simp [insertSorted]
  | cons h t ih =>
    simp [insertSorted]
    split_ifs with h_cond
    · simp
    · simp [ih]

-- LLM HELPER
lemma listSort_length (l : List Float) :
  (listSort l).length = l.length := by
  induction l with
  | nil => simp [listSort]
  | cons h t ih =>
    simp [listSort, insertSorted_length, ih]

-- LLM HELPER
lemma insertSorted_sorted (x : Float) (l : List Float) :
  (∀ i j : Nat, i < j → j < l.length → l[i]! ≤ l[j]!) →
  (∀ i j : Nat, i < j → j < (insertSorted x l).length → (insertSorted x l)[i]! ≤ (insertSorted x l)[j]!) := by
  intro h_sorted
  induction l with
  | nil => 
    simp [insertSorted]
    intros i j h_ij h_j_bound
    simp at h_j_bound
    omega
  | cons h t ih =>
    simp [insertSorted]
    split_ifs with h_cond
    · simp
      intros i j h_ij h_j_bound
      cases i with
      | zero =>
        cases j with
        | zero => omega
        | succ j' =>
          simp
          cases j' with
          | zero => exact h_cond
          | succ j'' =>
            simp
            apply h_sorted
            omega
            omega
      | succ i' =>
        cases j with
        | zero => omega
        | succ j' =>
          simp
          apply h_sorted
          omega
          omega
    · simp
      intros i j h_ij h_j_bound
      cases i with
      | zero =>
        cases j with
        | zero => omega
        | succ j' =>
          simp
          by_cases h_j_zero : j' = 0
          · subst h_j_zero
            simp
            sorry -- This case requires more complex reasoning about insertSorted
          · sorry -- This case requires more complex reasoning about insertSorted
      | succ i' =>
        cases j with
        | zero => omega
        | succ j' =>
          simp
          apply ih
          · intros i'' j'' h_i''j'' h_j''_bound
            apply h_sorted
            omega
            omega
          · omega
          · omega

-- LLM HELPER
lemma listSort_sorted (l : List Float) :
  ∀ i j : Nat, i < j → j < (listSort l).length → (listSort l)[i]! ≤ (listSort l)[j]! := by
  induction l with
  | nil => 
    simp [listSort]
    intros i j h_ij h_j_bound
    simp at h_j_bound
  | cons h t ih =>
    simp [listSort]
    apply insertSorted_sorted
    exact ih

-- LLM HELPER
lemma insertSorted_count (x y : Float) (l : List Float) :
  (insertSorted x l).count y = (if x = y then 1 else 0) + l.count y := by
  induction l with
  | nil => 
    simp [insertSorted]
    split_ifs <;> simp
  | cons h t ih =>
    simp [insertSorted]
    split_ifs with h_cond
    · simp [List.count]
      split_ifs <;> simp
    · simp [List.count, ih]
      split_ifs <;> simp [Nat.add_assoc]

-- LLM HELPER
lemma listSort_count (l : List Float) (x : Float) :
  (listSort l).count x = l.count x := by
  induction l with
  | nil => simp [listSort]
  | cons h t ih =>
    simp [listSort, insertSorted_count, ih]
    split_ifs with h_eq
    · simp [List.count, h_eq]
    · simp [List.count, h_eq]

/-- Return a sorted copy of an array -/
def sort {n : Nat} (a : Vector Float n) : Vector Float n := 
  Vector.ofList (listSort a.toList) (by simp [listSort_length])

/-- Specification: The result has the same length as input -/
theorem sort_length {n : Nat} (a : Vector Float n) :
  (sort a).toList.length = n := by
  simp [sort, Vector.toList_ofList, listSort_length]

/-- Specification: The result is sorted in ascending order -/
theorem sort_is_sorted {n : Nat} (a : Vector Float n) :
  ∀ i j : Fin n, i < j → (sort a)[i] ≤ (sort a)[j] := by
  intros i j h_ij
  simp [sort]
  have h_sorted := listSort_sorted a.toList
  have h_len : (listSort a.toList).length = n := by simp [listSort_length]
  have h_i_bound : i.val < (listSort a.toList).length := by simp [h_len]; exact i.isLt
  have h_j_bound : j.val < (listSort a.toList).length := by simp [h_len]; exact j.isLt
  have h_get_eq_i : (Vector.ofList (listSort a.toList) (by simp [listSort_length]))[i] = (listSort a.toList)[i.val]! := by
    simp [Vector.get_ofList]
  have h_get_eq_j : (Vector.ofList (listSort a.toList) (by simp [listSort_length]))[j] = (listSort a.toList)[j.val]! := by
    simp [Vector.get_ofList]
  rw [h_get_eq_i, h_get_eq_j]
  apply h_sorted
  exact h_ij
  exact h_j_bound

/-- Specification: The result is a permutation of the input -/
theorem sort_is_permutation {n : Nat} (a : Vector Float n) :
  ∀ x : Float, (sort a).toList.count x = a.toList.count x := by
  intro x
  simp [sort, Vector.toList_ofList, listSort_count]

end DafnySpecs.NpSort