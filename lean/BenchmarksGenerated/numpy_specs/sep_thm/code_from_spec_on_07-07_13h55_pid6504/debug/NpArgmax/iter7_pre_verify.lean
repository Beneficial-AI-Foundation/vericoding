/-
# NumPy Argmax Specification

Port of np_argmax.dfy to Lean 4
https://numpy.org/doc/stable/reference/generated/numpy.argmax.html
-/

namespace DafnySpecs.NpArgmax

-- LLM HELPER
def argmax_aux {n : Nat} (arr : Vector Float n) (k : Nat) (best_idx : Nat) : Nat :=
  if k = 0 then best_idx
  else 
    if h : k - 1 < n then
      if h_best : best_idx < n then
        let new_best := if arr[k - 1] > arr[best_idx] then k - 1 else best_idx
        argmax_aux arr (k - 1) new_best
      else best_idx
    else best_idx

-- LLM HELPER  
def find_argmax {n : Nat} (h : 0 < n) (arr : Vector Float n) : Nat :=
  argmax_aux arr n 0

-- LLM HELPER
lemma find_argmax_lt {n : Nat} (h : 0 < n) (arr : Vector Float n) : find_argmax h arr < n := by
  unfold find_argmax
  have : argmax_aux arr n 0 < n := by
    induction n with
    | zero => contradiction
    | succ n ih => 
      simp [argmax_aux]
      cases' n with n'
      · simp [argmax_aux]
        exact Nat.zero_lt_one
      · simp [argmax_aux]
        split_ifs with h1 h2
        · exact Nat.succ_lt_succ (Nat.lt_succ_iff.mp h1)
        · exact Nat.zero_lt_succ _
        · exact Nat.zero_lt_succ _
  exact this

/-- Returns the index of the maximum value along an axis.
    Returns index of first occurrence. -/
def argmax {n : Nat} (h : 0 < n) (arr : Vector Float n) : Fin n := 
  ⟨find_argmax h arr, find_argmax_lt h arr⟩

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
      simp [find_argmax, argmax_aux]
      have : i.val = 0 := by
        have : i.val < 1 := i.isLt
        exact Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ this)
      simp [this]
      have : find_argmax h arr = 0 := by simp [find_argmax, argmax_aux]
      simp [this] at hi
      have : ¬(0 < 0) := Nat.lt_irrefl 0
      exact absurd hi this
    · have : 0 < n := Nat.pos_of_ne_zero h_eq
      have arg_lt : find_argmax h arr < n + 1 := find_argmax_lt h arr
      have i_lt : i.val < find_argmax h arr := hi
      have : find_argmax h arr ≠ i.val := Ne.symm (Nat.ne_of_gt i_lt)
      have : arr[find_argmax h arr] ≥ arr[i] := by
        have : find_argmax h arr < n + 1 := find_argmax_lt h arr
        have : i.val < n + 1 := i.isLt
        exact Float.le_refl _
      exact Float.lt_of_le_of_ne this this

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
      simp [find_argmax, argmax_aux]
      have : i.val = 0 := by
        have : i.val < 1 := i.isLt
        exact Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ this)
      simp [this]
      have : find_argmax h arr = 0 := by simp [find_argmax, argmax_aux]
      simp [this] at hi
      have : ¬(0 < 0) := Nat.lt_irrefl 0
      exact absurd hi this
    · have : 0 < n := Nat.pos_of_ne_zero h_eq
      exact Float.le_refl _

end DafnySpecs.NpArgmax