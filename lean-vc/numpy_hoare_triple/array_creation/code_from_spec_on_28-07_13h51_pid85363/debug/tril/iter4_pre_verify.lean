import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.tril: Lower triangle of a matrix.

    Returns a copy of the input matrix with elements above the k-th diagonal zeroed.
    
    - k = 0 (default): zeros elements above the main diagonal
    - k < 0: zeros elements above the k-th diagonal below the main diagonal
    - k > 0: zeros elements above the k-th diagonal above the main diagonal
    
    For a matrix element at position (i, j):
    - It is kept if i >= j - k
    - It is zeroed if i < j - k
-/
def problem_spec {rows cols : Nat} (f : Vector (Vector Float cols) rows → Int → Id (Vector (Vector Float cols) rows)) 
    (m : Vector (Vector Float cols) rows) (k : Int := 0) : Prop :=
    ⦃⌜True⌝⦄
    f m k
    ⦃⇓result => ⌜-- Element-wise specification (core property)
                  (∀ (i : Fin rows) (j : Fin cols), 
                    (result.get i).get j = 
                      if (i : Int) ≥ (j : Int) - k then (m.get i).get j else 0) ∧
                  -- Sanity check: diagonal elements are preserved when k = 0
                  (k = 0 → ∀ i : Fin (min rows cols), 
                    have hi : i < rows := by apply Nat.lt_of_lt_of_le; exact i.isLt; exact Nat.min_le_left rows cols
                    have hj : i < cols := by apply Nat.lt_of_lt_of_le; exact i.isLt; exact Nat.min_le_right rows cols
                    (result.get ⟨i, hi⟩).get ⟨i, hj⟩ = (m.get ⟨i, hi⟩).get ⟨i, hj⟩) ∧
                  -- Sanity check: all elements preserved when k is very large
                  (k ≥ (cols : Int) → ∀ (i : Fin rows) (j : Fin cols), 
                    (result.get i).get j = (m.get i).get j) ∧
                  -- Sanity check: all elements zeroed when k is very negative
                  (k ≤ -(rows : Int) → ∀ (i : Fin rows) (j : Fin cols), 
                    (result.get i).get j = 0) ∧
                  -- Idempotency property: tril(tril(m, k), k) = tril(m, k)
                  (∀ (i : Fin rows) (j : Fin cols),
                    let twice_applied := f result k
                    ((twice_applied.run).get i).get j = (result.get i).get j)⌝⦄

def tril {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int := 0) : 
    Id (Vector (Vector Float cols) rows) :=
  Id.mk (Vector.ofFn (fun i : Fin rows =>
    Vector.ofFn (fun j : Fin cols =>
      if (i : Int) ≥ (j : Int) - k then
        (m.get i).get j
      else
        0)))

-- LLM HELPER
lemma tril_get_element {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int) 
    (i : Fin rows) (j : Fin cols) :
    ((tril m k).run.get i).get j = if (i : Int) ≥ (j : Int) - k then (m.get i).get j else 0 := by
  unfold tril
  simp [Vector.get_ofFn, Id.run]

-- LLM HELPER
lemma tril_idempotent {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int) :
    tril (tril m k).run k = tril m k := by
  apply Id.ext
  apply Vector.ext
  intro i
  apply Vector.ext
  intro j
  simp [tril_get_element]
  by_cases h : (i : Int) ≥ (j : Int) - k
  · simp [h]
  · simp [h]

theorem correctness {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int := 0) :
    problem_spec tril m k := by
  simp [problem_spec, Triple.val_app, Triple.bind_app, Triple.pure_app]
  constructor
  · intro i j
    exact tril_get_element m k i j
  constructor
  · intro hk i
    have hi : i < rows := by apply Nat.lt_of_lt_of_le; exact i.isLt; exact Nat.min_le_left rows cols
    have hj : i < cols := by apply Nat.lt_of_lt_of_le; exact i.isLt; exact Nat.min_le_right rows cols
    rw [tril_get_element]
    simp [hk]
    norm_cast
    simp
  constructor
  · intro hk i j
    rw [tril_get_element]
    simp only [ite_eq_left_iff, not_le]
    intro h
    exfalso
    have : (i : Int) ≥ (j : Int) - k := by
      have : (j : Int) ≤ (cols : Int) - 1 := by
        simp only [Int.coe_nat_sub]
        norm_cast
        exact Nat.le_sub_one_of_lt j.isLt
      linarith
    exact h this
  constructor
  · intro hk i j
    rw [tril_get_element]
    simp only [ite_eq_right_iff, not_ge]
    intro h
    exfalso
    have : (i : Int) < (j : Int) - k := by
      have : (i : Int) ≤ (rows : Int) - 1 := by
        simp only [Int.coe_nat_sub]
        norm_cast
        exact Nat.le_sub_one_of_lt i.isLt
      have : (j : Int) ≥ 0 := by norm_cast; exact Nat.zero_le j
      linarith
    exact h this
  · intro i j
    rw [tril_get_element, tril_get_element]
    by_cases h : (i : Int) ≥ (j : Int) - k
    · simp [h]
    · simp [h]