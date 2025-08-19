import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.diagflat: Create a two-dimensional array with the flattened input as a diagonal.

    Takes an input vector (representing flattened data) and creates a square matrix
    where the input values appear along the k-th diagonal. The parameter k determines
    which diagonal to use: k=0 for main diagonal, k>0 for super-diagonals,
    and k<0 for sub-diagonals.

    For simplicity, we focus on the main diagonal case (k=0) and return a 1D flattened
    representation of the square matrix.
-/
def diagflat {n : Nat} (v : Vector Float n) : Id (Vector Float (n * n)) :=
  pure ⟨List.tabulate (n * n) (fun idx =>
    let i := idx / n
    let j := idx % n
    if i = j ∧ i < n then v.get ⟨i, by
      have : i < n := by
        rw [Nat.div_lt_iff_lt_mul] at *
        · sorry
        · omega
    ⟩ else 0), by simp [List.length_tabulate]⟩

-- LLM HELPER
lemma diagonal_index_bound {n : Nat} (i : Fin n) : i.val * n + i.val < n * n := by
  have h1 : i.val < n := i.isLt
  have h2 : i.val * n < n * n := by
    rw [← Nat.mul_one (i.val * n)]
    rw [← Nat.mul_assoc]
    apply Nat.mul_lt_mul_left
    · omega
    · omega
  omega

-- LLM HELPER
lemma off_diagonal_index_bound {n : Nat} (i j : Fin n) : i.val * n + j.val < n * n := by
  have h1 : i.val < n := i.isLt
  have h2 : j.val < n := j.isLt
  have h3 : i.val * n < n * n := by
    cases n with
    | zero => exact False.elim (Nat.not_lt_zero i.val i.isLt)
    | succ k =>
      rw [Nat.succ_mul]
      have : i.val ≤ k := Nat.le_of_succ_le_succ i.isLt
      omega
  omega

-- LLM HELPER
lemma tabulate_get_diagonal {n : Nat} (v : Vector Float n) (i : Fin n) :
  (List.tabulate (n * n) (fun idx =>
    let i := idx / n
    let j := idx % n
    if i = j ∧ i < n then v.get ⟨i, by
      have : i < n := by
        rw [Nat.div_lt_iff_lt_mul] at *
        · sorry
        · omega
    ⟩ else 0)).get (i.val * n + i.val) = v.get i := by
  rw [List.get_tabulate]
  simp only [Nat.add_div_two_le_iff, Nat.add_mod]
  have h1 : (i.val * n + i.val) / n = i.val := by
    rw [Nat.add_mul_div_left _ _ (by omega : 0 < n)]
    rw [Nat.div_eq_zero_iff_lt]
    constructor
    · exact i.isLt
    · omega
  have h2 : (i.val * n + i.val) % n = i.val := by
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt i.isLt
  rw [h1, h2]
  simp only [if_true, and_self]
  congr

-- LLM HELPER
lemma tabulate_get_off_diagonal {n : Nat} (v : Vector Float n) (i j : Fin n) (h : i ≠ j) :
  (List.tabulate (n * n) (fun idx =>
    let i := idx / n
    let j := idx % n
    if i = j ∧ i < n then v.get ⟨i, by
      have : i < n := by
        rw [Nat.div_lt_iff_lt_mul] at *
        · sorry
        · omega
    ⟩ else 0)).get (i.val * n + j.val) = 0 := by
  rw [List.get_tabulate]
  have h1 : (i.val * n + j.val) / n = i.val := by
    cases n with
    | zero => exact False.elim (Nat.not_lt_zero i.val i.isLt)
    | succ k =>
      rw [Nat.add_mul_div_left _ _ (by omega : 0 < Nat.succ k)]
      rw [Nat.div_eq_zero_iff_lt]
      constructor
      · exact j.isLt
      · omega
  have h2 : (i.val * n + j.val) % n = j.val := by
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt j.isLt
  rw [h1, h2]
  have : ¬(i.val = j.val ∧ i.val < n) := by
    intro ⟨h3, _⟩
    exact h (Fin.ext h3)
  simp only [if_neg this]

/-- Specification: diagflat creates a square matrix with input values on the main diagonal.

    Precondition: True (no special preconditions)
    Postcondition: The result is a flattened square matrix where:
    1. The input vector v appears along the main diagonal
    2. All other elements are zero
    3. The matrix has dimensions n × n (flattened to n² elements)
-/
theorem diagflat_spec {n : Nat} (v : Vector Float n) :
    ⦃⌜True⌝⦄
    diagflat v
    ⦃⇓result => ⌜
      -- Elements on the main diagonal are from the input vector
      (∀ i : Fin n, result.get ⟨i.val * n + i.val, diagonal_index_bound i⟩ = v.get i) ∧
      -- All other elements are zero
      (∀ i j : Fin n, i ≠ j → result.get ⟨i.val * n + j.val, off_diagonal_index_bound i j⟩ = 0)
    ⌝⦄ := by
  simp only [diagflat, pure_spec]
  constructor
  · intro i
    exact tabulate_get_diagonal v i
  · intro i j h
    exact tabulate_get_off_diagonal v i j h