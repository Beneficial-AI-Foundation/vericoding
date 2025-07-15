/-
# NumPy Argmax Specification

Port of np_argmax.dfy to Lean 4
https://numpy.org/doc/stable/reference/generated/numpy.argmax.html
-/

namespace DafnySpecs.NpArgmax

-- LLM HELPER
def find_argmax {n : Nat} (h : 0 < n) (arr : Vector Float n) : Nat :=
  let rec aux (k : Nat) (best_idx : Nat) : Nat :=
    if k = 0 then best_idx
    else 
      if h : k - 1 < n then
        if h_best : best_idx < n then
          let new_best := if arr[k - 1] > arr[best_idx] then k - 1 else best_idx
          aux (k - 1) new_best
        else best_idx
      else best_idx
  aux n 0

-- LLM HELPER
lemma find_argmax_lt {n : Nat} (h : 0 < n) (arr : Vector Float n) : find_argmax h arr < n := by
  unfold find_argmax
  have : ∀ k best_idx, best_idx < n → (let rec aux (k : Nat) (best_idx : Nat) : Nat :=
    if k = 0 then best_idx
    else 
      if h : k - 1 < n then
        if h_best : best_idx < n then
          let new_best := if arr[k - 1] > arr[best_idx] then k - 1 else best_idx
          aux (k - 1) new_best
        else best_idx
      else best_idx
    aux k best_idx) < n := by
    intro k best_idx h_best
    induction k with
    | zero => simp; exact h_best
    | succ k ih =>
      simp
      split_ifs with h1 h2
      · simp
        by_cases h_comp : arr[k] > arr[best_idx]
        · simp [h_comp]; exact ih h1
        · simp [h_comp]; exact ih h_best
      · exact h_best
      · exact h_best
  exact this n 0 h

/-- Returns the index of the maximum value along an axis.
    Returns index of first occurrence. -/
def argmax {n : Nat} (h : 0 < n) (arr : Vector Float n) : Fin n := 
  ⟨find_argmax h arr, find_argmax_lt h arr⟩

-- LLM HELPER
lemma argmax_maximizes {n : Nat} (h : 0 < n) (arr : Vector Float n) (i : Fin n) :
  arr[i] ≤ arr[argmax h arr] := by
  have : ∀ j : Fin n, arr[j] ≤ arr[argmax h arr] := by
    intro j
    have : argmax h arr = ⟨find_argmax h arr, find_argmax_lt h arr⟩ := rfl
    simp [argmax]
    have : find_argmax h arr < n := find_argmax_lt h arr
    exact le_refl _
  exact this i

-- LLM HELPER
lemma lt_of_le_of_ne {α : Type*} [LinearOrder α] {a b : α} (h1 : a ≤ b) (h2 : a ≠ b) : a < b :=
  lt_of_le_of_ne h1 h2

/-- Specification: All elements before the maximum index are strictly less than the maximum -/
theorem argmax_is_max {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, i < argmax h arr → arr[argmax h arr] > arr[i] := by
  intro i hi
  induction n with
  | zero => contradiction
  | succ n ih =>
    simp [argmax] at hi
    simp [argmax]
    by_cases h_eq : n = 0
    · subst h_eq
      simp [find_argmax]
      have : i.val = 0 := by
        have : i.val < 1 := i.isLt
        exact Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ this)
      simp [this]
      have : find_argmax h arr = 0 := by simp [find_argmax]
      simp [this] at hi
      have : ¬(0 < 0) := Nat.lt_irrefl 0
      exact absurd hi this
    · have : 0 < n := Nat.pos_of_ne_zero h_eq
      have arg_lt : find_argmax h arr < n + 1 := find_argmax_lt h arr
      have i_lt : i.val < find_argmax h arr := hi
      have ne_eq : find_argmax h arr ≠ i.val := Ne.symm (Nat.ne_of_lt i_lt)
      have ge_val : arr[find_argmax h arr] ≥ arr[i] := by
        exact argmax_maximizes h arr i
      exact lt_of_le_of_ne ge_val ne_eq.symm

/-- Specification: All elements after the maximum index are less than or equal to the maximum -/
theorem argmax_is_first_max {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, argmax h arr < i → arr[argmax h arr] ≥ arr[i] := by
  intro i hi
  induction n with
  | zero => contradiction
  | succ n ih =>
    simp [argmax] at hi
    simp [argmax]
    by_cases h_eq : n = 0
    · subst h_eq
      simp [find_argmax]
      have : i.val = 0 := by
        have : i.val < 1 := i.isLt
        exact Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ this)
      simp [this]
      have : find_argmax h arr = 0 := by simp [find_argmax]
      simp [this] at hi
      have : ¬(0 < 0) := Nat.lt_irrefl 0
      exact absurd hi this
    · have : 0 < n := Nat.pos_of_ne_zero h_eq
      exact argmax_maximizes h arr i

end DafnySpecs.NpArgmax