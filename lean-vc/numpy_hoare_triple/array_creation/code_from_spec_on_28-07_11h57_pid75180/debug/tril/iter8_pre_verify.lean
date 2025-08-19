import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def wpure_spec (P : Prop) (computation : Id α) (Q : α → Prop) : Prop :=
  P → Q (computation.run)

-- LLM HELPER
notation "⦃" p "⦄" c "⦃⇓" r " => " q "⦄" => wpure_spec p c (fun r => q)

-- LLM HELPER
lemma Nat.lt_of_lt_min_left {a b n : Nat} (h : n < min a b) : n < a := by
  exact Nat.lt_of_lt_of_le h (Nat.min_le_left a b)

-- LLM HELPER
lemma Nat.lt_of_lt_min_right {a b n : Nat} (h : n < min a b) : n < b := by
  exact Nat.lt_of_lt_of_le h (Nat.min_le_right a b)

def tril {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int := 0) : 
    Id (Vector (Vector Float cols) rows) :=
  Id.pure (Vector.ofFn fun i => Vector.ofFn fun j => 
    if (i : Int) ≥ (j : Int) - k then (m.get i).get j else 0)

-- LLM HELPER
lemma tril_element_spec {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int) 
    (i : Fin rows) (j : Fin cols) :
    ((tril m k).run.get i).get j = if (i : Int) ≥ (j : Int) - k then (m.get i).get j else 0 := by
  simp [tril, Vector.get_ofFn]

-- LLM HELPER
lemma tril_idempotent {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int) :
    tril (tril m k).run k = tril m k := by
  ext i j
  simp [tril, Vector.get_ofFn]
  split_ifs with h
  · simp [tril_element_spec, h]
  · simp [tril_element_spec, h]

-- LLM HELPER
lemma diagonal_preserved {rows cols : Nat} (m : Vector (Vector Float cols) rows) 
    (i : Fin (min rows cols)) :
    let hi : i < rows := Nat.lt_of_lt_min_left i.isLt
    let hj : i < cols := Nat.lt_of_lt_min_right i.isLt
    ((tril m 0).run.get ⟨i, hi⟩).get ⟨i, hj⟩ = (m.get ⟨i, hi⟩).get ⟨i, hj⟩ := by
  simp [tril, Vector.get_ofFn]
  simp [Int.sub_zero, le_refl]

-- LLM HELPER
lemma all_preserved_large_k {rows cols : Nat} (m : Vector (Vector Float cols) rows) 
    (k : Int) (hk : k ≥ (cols : Int)) (i : Fin rows) (j : Fin cols) :
    ((tril m k).run.get i).get j = (m.get i).get j := by
  simp [tril, Vector.get_ofFn]
  simp only [ite_eq_left_iff, not_ge, ge_iff_le]
  intro h
  have : (j : Int) - k ≤ (j : Int) - (cols : Int) := Int.sub_le_sub_left hk _
  have : (j : Int) - (cols : Int) < 0 := by
    simp [Int.sub_neg_iff_lt]
    norm_cast
    exact j.isLt
  have : (j : Int) - k < 0 := lt_of_le_of_lt this ‹(j : Int) - (cols : Int) < 0›
  have : (i : Int) ≥ 0 := by norm_cast; exact Nat.zero_le _
  linarith

-- LLM HELPER
lemma all_zeroed_small_k {rows cols : Nat} (m : Vector (Vector Float cols) rows) 
    (k : Int) (hk : k ≤ -(rows : Int)) (i : Fin rows) (j : Fin cols) :
    ((tril m k).run.get i).get j = 0 := by
  simp [tril, Vector.get_ofFn]
  simp only [ite_eq_right_iff, not_ge, ge_iff_le]
  intro h
  exfalso
  have : (i : Int) < (rows : Int) := by norm_cast; exact i.isLt
  have : (j : Int) ≥ 0 := by norm_cast; exact Nat.zero_le _
  have : (j : Int) - k ≥ (j : Int) - (-(rows : Int)) := Int.sub_le_sub_left (le_neg_of_le_neg hk) _
  have : (j : Int) - (-(rows : Int)) = (j : Int) + (rows : Int) := by ring
  rw [this] at *
  have : (j : Int) + (rows : Int) ≥ (rows : Int) := by linarith
  linarith

def problem_spec {rows cols : Nat} (tril_impl : Vector (Vector Float cols) rows → Int → Id (Vector (Vector Float cols) rows)) 
    (m : Vector (Vector Float cols) rows) (k : Int := 0) : Prop :=
  wpure_spec True (tril_impl m k) (fun result => 
    (∀ (i : Fin rows) (j : Fin cols), 
      (result.get i).get j = if (j : Int) - k ≤ (i : Int) then (m.get i).get j else 0) ∧
    (k = 0 → ∀ i : Fin (min rows cols), 
      let hi := Nat.lt_of_lt_min_left i.isLt
      let hj := Nat.lt_of_lt_min_right i.isLt
      (result.get ⟨i, hi⟩).get ⟨i, hj⟩ = (m.get ⟨i, hi⟩).get ⟨i, hj⟩) ∧
    ((cols : Int) ≤ k → ∀ (i : Fin rows) (j : Fin cols), 
      (result.get i).get j = (m.get i).get j) ∧
    (k ≤ -(rows : Int) → ∀ (i : Fin rows) (j : Fin cols), 
      (result.get i).get j = 0) ∧
    (∀ (i : Fin rows) (j : Fin cols),
      (Vector.get (tril_impl result k).run i).get j = (result.get i).get j))

theorem correctness {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int := 0) : 
    problem_spec (fun m k => tril m k) m k := by
  simp [problem_spec, wpure_spec]
  constructor
  · intro i j
    rw [tril_element_spec]
    simp only [ge_iff_le, Int.le_sub_iff_add_le]
    rw [if_congr (Int.le_sub_iff_add_le.symm)]
    simp [ge_iff_le]
  constructor
  · intro hk i
    have hi := Nat.lt_of_lt_min_left i.isLt
    have hj := Nat.lt_of_lt_min_right i.isLt
    rw [hk]
    exact diagonal_preserved m i
  constructor
  · exact all_preserved_large_k m k
  constructor
  · exact all_zeroed_small_k m k
  · intro i j
    have h := tril_idempotent m k
    simp [h]