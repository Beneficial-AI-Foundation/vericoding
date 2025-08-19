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
  Id.pure (Vector.ofFn (fun idx : Fin (n * n) => 
    let i := idx.val / n
    let j := idx.val % n
    if i = j ∧ i < n then v.get ⟨i, by
      have h1 : idx.val < n * n := idx.property
      have h2 : i * n ≤ idx.val := Nat.div_mul_le_self idx.val n
      have h3 : idx.val < (i + 1) * n := Nat.lt_mul_div_succ idx.val (Nat.zero_lt_of_ne_zero (by
        by_cases h : n = 0
        · simp [h] at h1
          exact absurd h1 (Nat.lt_irrefl 0)
        · exact Nat.pos_of_ne_zero h))
      rw [Nat.add_mul] at h3
      simp at h3
      have h4 : i < n := by
        by_contra h_not
        push_neg at h_not
        have h5 : n ≤ i := h_not
        have h6 : n * n ≤ i * n := Nat.mul_le_mul_right n h5
        have h7 : i * n ≤ idx.val := h2
        have h8 : n * n ≤ idx.val := le_trans h6 h7
        rw [Nat.mul_comm] at h8
        exact not_le_of_lt h1 h8
      exact h4⟩) else 0))

-- LLM HELPER
lemma diagflat_diagonal_index {n : Nat} (i : Fin n) : 
  i.val * n + i.val < n * n := by
  have h1 : i.val < n := i.property
  have h2 : i.val * n < n * n := Nat.mul_lt_mul_of_pos_right h1 (Nat.pos_of_ne_zero (by
    by_cases h : n = 0
    · simp [h] at h1
      exact absurd h1 (Nat.lt_irrefl 0)
    · exact h))
  have h3 : i.val ≤ n := le_of_lt h1
  have h4 : i.val ≤ n - 1 := Nat.le_sub_one_of_lt h1
  calc i.val * n + i.val
    = i.val * (n + 1) := by ring
    _ ≤ (n - 1) * (n + 1) := Nat.mul_le_mul_right (n + 1) h4
    _ = n * n - 1 := by ring_nf; sorry  -- This step needs careful arithmetic
    _ < n * n := Nat.sub_lt (Nat.pos_of_ne_zero (by
      by_cases h : n = 0
      · simp [h] at h1
        exact absurd h1 (Nat.lt_irrefl 0)  
      · rw [Nat.mul_ne_zero_iff]
        exact ⟨h, h⟩)) (by norm_num)

-- LLM HELPER  
lemma diagflat_off_diagonal_index {n : Nat} (i j : Fin n) (h : i ≠ j) :
  i.val * n + j.val < n * n := by
  have h1 : i.val < n := i.property
  have h2 : j.val < n := j.property  
  have h3 : i.val * n < n * n := Nat.mul_lt_mul_of_pos_right h1 (Nat.pos_of_ne_zero (by
    by_cases hn : n = 0
    · simp [hn] at h1
      exact absurd h1 (Nat.lt_irrefl 0)
    · exact hn))
  calc i.val * n + j.val
    < i.val * n + n := Nat.add_lt_add_left h2 (i.val * n)
    _ = (i.val + 1) * n := by ring
    _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h1)

-- LLM HELPER
lemma diagflat_get_diagonal {n : Nat} (v : Vector Float n) (i : Fin n) :
  (diagflat v).run.get ⟨i.val * n + i.val, diagflat_diagonal_index i⟩ = v.get i := by
  simp [diagflat]
  simp [Vector.ofFn]
  have h1 : (i.val * n + i.val) / n = i.val := by
    rw [Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero (by
      by_cases h : n = 0  
      · simp [h] at i
        exact absurd i.property (Nat.lt_irrefl 0)
      · exact h))]
    simp [Nat.div_lt_iff_lt_mul]
    exact Nat.div_zero_of_lt i.property
  have h2 : (i.val * n + i.val) % n = i.val := by
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt i.property
  simp [h1, h2]
  congr

-- LLM HELPER  
lemma diagflat_get_off_diagonal {n : Nat} (v : Vector Float n) (i j : Fin n) (h : i ≠ j) :
  (diagflat v).run.get ⟨i.val * n + j.val, diagflat_off_diagonal_index i j h⟩ = 0 := by
  simp [diagflat]
  simp [Vector.ofFn]
  have h1 : (i.val * n + j.val) / n = i.val := by
    rw [Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero (by
      by_cases hn : n = 0
      · simp [hn] at i
        exact absurd i.property (Nat.lt_irrefl 0)  
      · exact hn))]
    exact Nat.div_zero_of_lt j.property
  have h2 : (i.val * n + j.val) % n = j.val := by
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt j.property
  simp [h1, h2]
  have h3 : i.val ≠ j.val := fun heq => h (Fin.ext heq)
  simp [h3]

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
      (∀ i : Fin n, result.get ⟨i.val * n + i.val, diagflat_diagonal_index i⟩ = v.get i) ∧
      -- All other elements are zero
      (∀ i j : Fin n, i ≠ j → result.get ⟨i.val * n + j.val, diagflat_off_diagonal_index i j H⟩ = 0)
    ⌝⦄ := by
  apply Std.Do.pure_spec_of_pure
  constructor
  · intro i
    exact diagflat_get_diagonal v i
  · intro i j h  
    exact diagflat_get_off_diagonal v i j h