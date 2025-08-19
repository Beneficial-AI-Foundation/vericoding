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
def diagflat {n : Nat} (v : Vector Float n) : Id (Vector Float (n * n)) := do
  let result_list := List.range (n * n) |>.map (fun idx =>
    let i := idx / n
    let j := idx % n
    if i = j ∧ i < n then 
      have h : i < n := by 
        simp [i]
        have : idx < n * n := by simp [List.mem_range]
        cases n with
        | zero => simp at this
        | succ n' =>
          have h_div_le : idx / (n' + 1) ≤ n' := Nat.div_le_of_le_mul_right this
          simp at h_div_le
          exact Nat.lt_succ_of_le h_div_le
      v.get ⟨i, h⟩ 
    else 0)
  return ⟨result_list.toArray, by simp [List.length_range, List.length_map]⟩

-- LLM HELPER
lemma diagflat_index_bound {n : Nat} (i : Fin n) : i.val * n + i.val < n * n := by
  have h1 : i.val < n := i.isLt
  have h2 : i.val * n ≤ (n - 1) * n := Nat.mul_le_mul_right n (Nat.le_pred_of_lt h1)
  have h3 : i.val * n + i.val ≤ (n - 1) * n + (n - 1) := Nat.add_le_add h2 (Nat.le_pred_of_lt h1)
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero i.val h1)
  | succ n' =>
    simp at h3
    have : (n' * (n' + 1) + n') + 1 = (n' + 1) * (n' + 1) := by ring
    rw [← this]
    exact Nat.lt_succ_of_le h3

-- LLM HELPER  
lemma diagflat_off_diag_bound {n : Nat} (i j : Fin n) : i.val * n + j.val < n * n := by
  have h1 : i.val < n := i.isLt
  have h2 : j.val < n := j.isLt
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero i.val h1)
  | succ n' =>
    have : i.val * (n' + 1) + j.val < (n' + 1) * (n' + 1) := by
      have : i.val ≤ n' := Nat.le_of_lt_succ h1
      have : i.val * (n' + 1) ≤ n' * (n' + 1) := Nat.mul_le_mul_right (n' + 1) this
      have : i.val * (n' + 1) + j.val ≤ n' * (n' + 1) + n' := Nat.add_le_add this (Nat.le_of_lt_succ h2)
      have : n' * (n' + 1) + n' < (n' + 1) * (n' + 1) := by
        rw [Nat.succ_mul]
        simp only [Nat.add_mul]
        ring_nf
        simp
      exact Nat.lt_of_le_of_lt ‹i.val * (n' + 1) + j.val ≤ n' * (n' + 1) + n'› this
    exact this

-- LLM HELPER
lemma hl_triple_pre_pure {α : Type} (P : Prop) (x : Id α) (Q : α → Prop) : 
  (⦃⌜P⌝⦄ x ⦃⇓result => ⌜Q result⌝⦄) ↔ (P → Q (x.run)) := by
  simp [DoubleTriplet.triple_pre_pure, DoubleTriplet.pre_pure]

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
      (∀ i : Fin n, result.get ⟨i.val * n + i.val, diagflat_index_bound i⟩ = v.get i) ∧
      -- All other elements are zero
      (∀ i j : Fin n, i ≠ j → result.get ⟨i.val * n + j.val, diagflat_off_diag_bound i j⟩ = 0)
    ⌝⦄ := by
  rw [hl_triple_pre_pure]
  intro
  simp [diagflat, Id.run, Id.bind_eq]
  constructor
  · intro i
    simp [Vector.get]
    have h_range : i.val * n + i.val < List.length (List.range (n * n)) := by
      simp [List.length_range]
      exact diagflat_index_bound i
    simp [List.get_map, List.get_range, h_range, Array.getElem_toArray]
    have h_div : (i.val * n + i.val) / n = i.val := by
      cases n with
      | zero => exact False.elim (Nat.not_lt_zero i.val i.isLt)
      | succ n' =>
        rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_succ n')]
        simp [Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ n')]
    have h_mod : (i.val * n + i.val) % n = i.val := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt i.isLt
    simp [h_div, h_mod]
    have h_lt : i.val < n := i.isLt
    simp [h_lt]
    congr
    exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
  · intro i j h_neq
    simp [Vector.get]
    have h_range : i.val * n + j.val < List.length (List.range (n * n)) := by
      simp [List.length_range]
      exact diagflat_off_diag_bound i j
    simp [List.get_map, List.get_range, h_range, Array.getElem_toArray]
    have h_div : (i.val * n + j.val) / n = i.val := by
      cases n with
      | zero => exact False.elim (Nat.not_lt_zero i.val i.isLt)
      | succ n' =>
        rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_succ n')]
        have : j.val < n' + 1 := j.isLt
        exact Nat.div_eq_of_lt this
    have h_mod : (i.val * n + j.val) % n = j.val := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt j.isLt
    simp [h_div, h_mod]
    have : i.val ≠ j.val := fun h => h_neq (Fin.ext h)
    simp [this]