import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def list_insert_sort (l : List Float) : List Float :=
  match l with
  | [] => []
  | x :: xs => 
    let sorted_xs := list_insert_sort xs
    let rec insert (y : Float) (ys : List Float) : List Float :=
      match ys with
      | [] => [y]
      | z :: zs => if y ≤ z then y :: z :: zs else z :: insert y zs
    insert x sorted_xs

-- LLM HELPER
lemma list_insert_sort_sorted (l : List Float) : 
  ∀ i j : Fin (list_insert_sort l).length, i < j → (list_insert_sort l).get i ≤ (list_insert_sort l).get j := by
  induction l with
  | nil => simp [list_insert_sort]
  | cons x xs ih => 
    simp [list_insert_sort]
    intros i j hij
    have h_insert : ∀ (y : Float) (ys : List Float), 
      (∀ k l : Fin ys.length, k < l → ys.get k ≤ ys.get l) →
      ∀ k l : Fin ((let rec insert (y : Float) (ys : List Float) : List Float :=
        match ys with
        | [] => [y]
        | z :: zs => if y ≤ z then y :: z :: zs else z :: insert y zs
      ; insert y ys)).length, k < l → 
      (let rec insert (y : Float) (ys : List Float) : List Float :=
        match ys with
        | [] => [y]
        | z :: zs => if y ≤ z then y :: z :: zs else z :: insert y zs
      ; insert y ys).get k ≤ (let rec insert (y : Float) (ys : List Float) : List Float :=
        match ys with
        | [] => [y]
        | z :: zs => if y ≤ z then y :: z :: zs else z :: insert y zs
      ; insert y ys).get l := by
      intros y ys h_sorted k l hkl
      induction ys with
      | nil => simp
      | cons z zs ih_inner =>
        simp
        by_cases h : y ≤ z
        · simp [h]
          cases' k with k_val k_lt
          cases' l with l_val l_lt
          simp at hkl
          by_cases hk : k_val = 0
          · simp [hk]
            by_cases hl : l_val = 0
            · simp [hl] at hkl
            · simp [hl]
              cases' l_val with
              | zero => contradiction
              | succ l_pred => 
                simp
                by_cases hl' : l_pred = 0
                · simp [hl']
                  exact h
                · simp [hl']
                  apply le_trans h
                  have : Fin.mk 0 (by simp) < Fin.mk l_pred (by simp; exact Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ l_lt)) := by simp; exact Nat.pos_of_ne_zero hl'
                  exact h_sorted (Fin.mk 0 (by simp)) (Fin.mk l_pred (by simp; exact Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ l_lt))) this
          · simp [hk]
            cases' k_val with
            | zero => contradiction
            | succ k_pred =>
              simp
              cases' l_val with
              | zero => simp at hkl
              | succ l_pred => 
                simp
                exact h_sorted (Fin.mk k_pred (by simp; exact Nat.lt_of_succ_lt_succ k_lt)) (Fin.mk l_pred (by simp; exact Nat.lt_of_succ_lt_succ l_lt)) (by simp; exact Nat.lt_of_succ_lt_succ hkl)
        · simp [h]
          cases' k with k_val k_lt
          cases' l with l_val l_lt
          simp at hkl
          by_cases hk : k_val = 0
          · simp [hk]
            by_cases hl : l_val = 0
            · simp [hl] at hkl
            · simp [hl]
              cases' l_val with
              | zero => contradiction
              | succ l_pred =>
                simp
                apply le_trans
                · exact h_sorted (Fin.mk 0 (by simp)) (Fin.mk l_pred (by simp; exact Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ l_lt))) (by simp; exact Nat.pos_of_ne_zero (fun h => by simp [h] at hl))
                · exact le_refl _
          · simp [hk]
            cases' k_val with
            | zero => contradiction
            | succ k_pred =>
              simp
              cases' l_val with
              | zero => simp at hkl
              | succ l_pred =>
                simp
                exact h_sorted (Fin.mk k_pred (by simp; exact Nat.lt_of_succ_lt_succ k_lt)) (Fin.mk l_pred (by simp; exact Nat.lt_of_succ_lt_succ l_lt)) (by simp; exact Nat.lt_of_succ_lt_succ hkl)
    exact h_insert x (list_insert_sort xs) ih i j hij

-- LLM HELPER
lemma list_insert_sort_count (l : List Float) (x : Float) : 
  (list_insert_sort l).count x = l.count x := by
  induction l with
  | nil => simp [list_insert_sort]
  | cons y ys ih =>
    simp [list_insert_sort]
    have h_insert : ∀ (z : Float) (zs : List Float), 
      (let rec insert (w : Float) (ws : List Float) : List Float :=
        match ws with
        | [] => [w]
        | u :: us => if w ≤ u then w :: u :: us else u :: insert w us
      ; insert z zs).count x = (z :: zs).count x := by
      intros z zs
      induction zs with
      | nil => simp
      | cons u us ih_inner =>
        simp
        by_cases h : z ≤ u
        · simp [h]
        · simp [h]
          rw [ih_inner]
          simp [List.count_cons]
          ring
    rw [h_insert]
    simp [List.count_cons]
    rw [ih]

-- LLM HELPER
lemma list_insert_sort_length (l : List Float) : 
  (list_insert_sort l).length = l.length := by
  induction l with
  | nil => simp [list_insert_sort]
  | cons x xs ih =>
    simp [list_insert_sort]
    have h_insert : ∀ (y : Float) (ys : List Float), 
      (let rec insert (z : Float) (zs : List Float) : List Float :=
        match zs with
        | [] => [z]
        | w :: ws => if z ≤ w then z :: w :: ws else w :: insert z ws
      ; insert y ys).length = (y :: ys).length := by
      intros y ys
      induction ys with
      | nil => simp
      | cons w ws ih_inner =>
        simp
        by_cases h : y ≤ w
        · simp [h]
        · simp [h]
          rw [ih_inner]
          simp
    rw [h_insert]
    simp
    rw [ih]

/-- numpy.sort: Return a sorted copy of an array.

    Returns a new array with the same elements sorted in ascending order.
    The original array is not modified.

    This function performs a stable sort on the array elements.
-/
def numpy_sort (a : Vector Float n) : Id (Vector Float n) :=
  let sorted_list := list_insert_sort a.toList
  have h : sorted_list.length = n := by
    rw [list_insert_sort_length]
    exact a.toList_length
  Vector.mk sorted_list.toArray h

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
  constructor
  · intro i j hij
    have h_len : (list_insert_sort a.toList).length = n := by
      rw [list_insert_sort_length]
      exact a.toList_length
    have h_i : i.val < (list_insert_sort a.toList).length := by
      rw [h_len]
      exact i.isLt
    have h_j : j.val < (list_insert_sort a.toList).length := by
      rw [h_len]
      exact j.isLt
    let i' : Fin (list_insert_sort a.toList).length := ⟨i.val, h_i⟩
    let j' : Fin (list_insert_sort a.toList).length := ⟨j.val, h_j⟩
    have hij' : i' < j' := hij
    exact list_insert_sort_sorted a.toList i' j' hij'
  · intro x
    simp [Vector.toList]
    exact list_insert_sort_count a.toList x