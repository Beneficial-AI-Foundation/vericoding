import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

def problem_spec {n : Nat} (impl : Vector Float n → Id (Vector Float (n * n))) (v : Vector Float n) : Prop :=
  ∃ result, impl v = Id.pure result ∧
    (∀ i : Fin n, result.get ⟨i.val * n + i.val, by
      have h1 : i.val < n := i.property
      have h2 : i.val * n < n * n := by
        cases' Nat.eq_zero_or_pos n with h h
        · subst h
          exact absurd h1 (Nat.lt_irrefl 0)
        · exact Nat.mul_lt_mul_of_pos_right h1 h
      calc i.val * n + i.val
        < i.val * n + n := Nat.add_lt_add_left h1 (i.val * n)
        _ = (i.val + 1) * n := by rw [Nat.add_mul]
        _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h1)⟩ = v.get i) ∧
    (∀ i j : Fin n, i ≠ j → result.get ⟨i.val * n + j.val, by
      have h1 : i.val < n := i.property
      have h2 : j.val < n := j.property  
      have h3 : i.val * n < n * n := by
        cases' Nat.eq_zero_or_pos n with hn hn
        · subst hn
          exact absurd h1 (Nat.lt_irrefl 0)
        · exact Nat.mul_lt_mul_of_pos_right h1 hn
      calc i.val * n + j.val
        < i.val * n + n := Nat.add_lt_add_left h2 (i.val * n)
        _ = (i.val + 1) * n := by rw [Nat.add_mul]
        _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h1)⟩ = 0)

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
    if h : i = j ∧ i < n then v.get ⟨i, h.2⟩ else 0))

-- LLM HELPER
lemma diagflat_diagonal_index {n : Nat} (i : Fin n) : 
  i.val * n + i.val < n * n := by
  have h1 : i.val < n := i.property
  have h2 : i.val * n < n * n := by
    cases' Nat.eq_zero_or_pos n with h h
    · subst h
      exact absurd h1 (Nat.lt_irrefl 0)
    · exact Nat.mul_lt_mul_of_pos_right h1 h
  have h3 : i.val < n := h1
  calc i.val * n + i.val
    < i.val * n + n := Nat.add_lt_add_left h3 (i.val * n)
    _ = (i.val + 1) * n := by rw [Nat.add_mul]
    _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h1)

-- LLM HELPER  
lemma diagflat_off_diagonal_index {n : Nat} (i j : Fin n) (h : i ≠ j) :
  i.val * n + j.val < n * n := by
  have h1 : i.val < n := i.property
  have h2 : j.val < n := j.property  
  have h3 : i.val * n < n * n := by
    cases' Nat.eq_zero_or_pos n with hn hn
    · subst hn
      exact absurd h1 (Nat.lt_irrefl 0)
    · exact Nat.mul_lt_mul_of_pos_right h1 hn
  calc i.val * n + j.val
    < i.val * n + n := Nat.add_lt_add_left h2 (i.val * n)
    _ = (i.val + 1) * n := by rw [Nat.add_mul]
    _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h1)

-- LLM HELPER
lemma diagflat_get_diagonal {n : Nat} (v : Vector Float n) (i : Fin n) :
  let result := Vector.ofFn (fun idx : Fin (n * n) => 
    let i_idx := idx.val / n
    let j_idx := idx.val % n
    if h : i_idx = j_idx ∧ i_idx < n then v.get ⟨i_idx, h.2⟩ else 0)
  result.get ⟨i.val * n + i.val, diagflat_diagonal_index i⟩ = v.get i := by
  simp [Vector.ofFn_val]
  have h1 : (i.val * n + i.val) / n = i.val := by
    cases' Nat.eq_zero_or_pos n with hn hn
    · subst hn
      exact absurd i.property (Nat.lt_irrefl 0)
    · rw [Nat.add_mul_div_left _ _ hn]
      exact Nat.div_eq_zero_of_lt i.property
  have h2 : (i.val * n + i.val) % n = i.val := by
    cases' Nat.eq_zero_or_pos n with hn hn  
    · subst hn
      exact absurd i.property (Nat.lt_irrefl 0)
    · rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt i.property
  rw [h1, h2]
  have h3 : i.val = i.val := rfl
  have h4 : i.val < n := i.property
  simp [if_pos ⟨h3, h4⟩]

-- LLM HELPER  
lemma diagflat_get_off_diagonal {n : Nat} (v : Vector Float n) (i j : Fin n) (h : i ≠ j) :
  let result := Vector.ofFn (fun idx : Fin (n * n) => 
    let i_idx := idx.val / n
    let j_idx := idx.val % n
    if h_eq : i_idx = j_idx ∧ i_idx < n then v.get ⟨i_idx, h_eq.2⟩ else 0)
  result.get ⟨i.val * n + j.val, diagflat_off_diagonal_index i j h⟩ = 0 := by
  simp [Vector.ofFn_val]
  have h1 : (i.val * n + j.val) / n = i.val := by
    cases' Nat.eq_zero_or_pos n with hn hn
    · subst hn
      exact absurd i.property (Nat.lt_irrefl 0)
    · rw [Nat.add_mul_div_left _ _ hn]
      exact Nat.div_eq_zero_of_lt j.property
  have h2 : (i.val * n + j.val) % n = j.val := by
    cases' Nat.eq_zero_or_pos n with hn hn
    · subst hn
      exact absurd i.property (Nat.lt_irrefl 0)
    · rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt j.property
  rw [h1, h2]
  have h3 : i.val ≠ j.val := fun heq => h (Fin.ext heq)
  simp [if_neg]
  intro h_conj
  exact h3 h_conj.1

/-- Specification: diagflat creates a square matrix with input values on the main diagonal.

    Precondition: True (no special preconditions)
    Postcondition: The result is a flattened square matrix where:
    1. The input vector v appears along the main diagonal
    2. All other elements are zero
    3. The matrix has dimensions n × n (flattened to n² elements)
-/
theorem diagflat_spec {n : Nat} (v : Vector Float n) :
    problem_spec diagflat v := by
  use (Vector.ofFn (fun idx : Fin (n * n) => 
    let i := idx.val / n
    let j := idx.val % n
    if h : i = j ∧ i < n then v.get ⟨i, h.2⟩ else 0))
  constructor
  · rfl
  constructor
  · intro i
    exact diagflat_get_diagonal v i
  · intro i j h  
    exact diagflat_get_off_diagonal v i j h