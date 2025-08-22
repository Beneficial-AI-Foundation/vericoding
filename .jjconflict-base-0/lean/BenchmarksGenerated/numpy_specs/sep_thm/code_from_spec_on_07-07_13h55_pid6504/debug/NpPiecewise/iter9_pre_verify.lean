/-
# NumPy Piecewise Specification

Port of np_piecewise.dfy to Lean 4
-/

namespace DafnySpecs.NpPiecewise

-- LLM HELPER
def find_first_true_index {m : Nat} (condlist : Vector (Float → Bool) m) (val : Float) : Option Nat :=
  let rec helper (i : Nat) : Option Nat :=
    if h : i < m then
      if condlist[i]! val then
        some i
      else
        helper (i + 1)
    else
      none
  helper 0

-- LLM HELPER
def apply_piecewise_element {m : Nat} (val : Float) (condlist : Vector (Float → Bool) m) (funclist : Vector (Float → Float) m) : Float :=
  match find_first_true_index condlist val with
  | some idx => funclist[idx]! val
  | none => val

/-- Apply piecewise function based on conditions -/
def piecewise {n m : Nat} (x : Vector Float n) (condlist : Vector (Float → Bool) m) (funclist : Vector (Float → Float) m) : Vector Float n :=
  Vector.ofFn (fun (i : Fin n) => apply_piecewise_element (x[i]!) condlist funclist)

-- LLM HELPER
lemma vector_ofFn_length {n : Nat} (f : Fin n → Float) : 
  (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn, Vector.toList]

/-- Specification: The result has same length as input -/
theorem piecewise_length {n m : Nat} (x : Vector Float n) (condlist : Vector (Float → Bool) m) (funclist : Vector (Float → Float) m)
  (h : m = m) :
  let ret := piecewise x condlist funclist
  ret.toList.length = n := by
  simp [piecewise]
  exact vector_ofFn_length _

-- LLM HELPER
lemma find_first_true_index_sound {m : Nat} (condlist : Vector (Float → Bool) m) (val : Float) (j : Nat) :
  find_first_true_index condlist val = some j → j < m ∧ condlist[j]! val := by
  unfold find_first_true_index
  let rec helper_sound (i : Nat) : find_first_true_index.helper condlist val i = some j → j < m ∧ condlist[j]! val := by
    intro h_eq
    unfold find_first_true_index.helper at h_eq
    if h_i : i < m then
      simp [h_i] at h_eq
      if h_cond : condlist[i]! val then
        simp [h_cond] at h_eq
        rw [← h_eq]
        exact ⟨h_i, h_cond⟩
      else
        simp [h_cond] at h_eq
        exact helper_sound (i + 1) h_eq
    else
      simp [h_i] at h_eq
  exact helper_sound 0

-- LLM HELPER
lemma vector_ofFn_get {n : Nat} (f : Fin n → Float) (i : Nat) (h : i < n) :
  (Vector.ofFn f)[i]! = f ⟨i, h⟩ := by
  simp [Vector.get, Vector.ofFn]

-- LLM HELPER
lemma find_first_true_index_minimal {m : Nat} (condlist : Vector (Float → Bool) m) (val : Float) (j k : Nat) :
  find_first_true_index condlist val = some j → k < j → ¬(condlist[k]! val) := by
  unfold find_first_true_index
  let rec helper_minimal (i : Nat) : find_first_true_index.helper condlist val i = some j → ∀ k, i ≤ k → k < j → ¬(condlist[k]! val) := by
    intro h_eq k h_le h_lt
    unfold find_first_true_index.helper at h_eq
    if h_i : i < m then
      simp [h_i] at h_eq
      if h_cond : condlist[i]! val then
        simp [h_cond] at h_eq
        rw [← h_eq] at h_lt
        have : k < k := by
          have : i ≤ k := h_le
          have : k < i := h_lt
          omega
        omega
      else
        simp [h_cond] at h_eq
        if h_eq_i : i = k then
          rw [← h_eq_i]
          exact h_cond
        else
          have h_succ : i + 1 ≤ k := by omega
          exact helper_minimal (i + 1) h_eq k h_succ h_lt
    else
      simp [h_i] at h_eq
  intro h_eq h_lt
  exact helper_minimal 0 h_eq k (Nat.zero_le k) h_lt

-- LLM HELPER
lemma find_first_true_index_complete {m : Nat} (condlist : Vector (Float → Bool) m) (val : Float) (j : Nat) :
  j < m → condlist[j]! val → ∃ k, find_first_true_index condlist val = some k ∧ k ≤ j := by
  intro h_j h_cond
  unfold find_first_true_index
  let rec helper_complete (i : Nat) : i ≤ j → ∃ k, find_first_true_index.helper condlist val i = some k ∧ k ≤ j := by
    intro h_le
    unfold find_first_true_index.helper
    if h_i : i < m then
      simp [h_i]
      if h_cond_i : condlist[i]! val then
        simp [h_cond_i]
        exact ⟨i, rfl, h_le⟩
      else
        simp [h_cond_i]
        if h_eq : i = j then
          rw [h_eq] at h_cond_i
          exact False.elim (h_cond_i h_cond)
        else
          have h_succ : i + 1 ≤ j := by omega
          exact helper_complete (i + 1) h_succ
    else
      have : i ≤ j := h_le
      have : j < m := h_j
      have : i < m := Nat.lt_of_le_of_lt this ‹j < m›
      exact False.elim (h_i this)
  exact helper_complete 0 (Nat.zero_le j)

/-- Specification: Function application based on conditions -/
theorem piecewise_spec {n m : Nat} (x : Vector Float n) (condlist : Vector (Float → Bool) m) (funclist : Vector (Float → Float) m)
  (h : m = m) :
  let ret := piecewise x condlist funclist
  ∀ i j : Nat, i < n → j < m →
    condlist[j]! (x[i]!) → ret[i]! = funclist[j]! (x[i]!) := by
  intro i j h_i h_j h_cond
  simp [piecewise]
  rw [vector_ofFn_get]
  simp [apply_piecewise_element]
  cases h_find : find_first_true_index condlist (x[i]!) with
  | none => 
    have ⟨k, h_k_eq, h_k_le⟩ := find_first_true_index_complete condlist (x[i]!) j h_j h_cond
    rw [h_find] at h_k_eq
    cases h_k_eq
  | some k =>
    have ⟨h_k_lt, h_k_cond⟩ := find_first_true_index_sound condlist (x[i]!) k h_find
    have h_k_le_j : k ≤ j := by
      by_contra h_not_le
      have h_j_lt_k : j < k := Nat.lt_of_not_le h_not_le
      have h_not_cond : ¬(condlist[j]! (x[i]!)) := find_first_true_index_minimal condlist (x[i]!) k j h_find h_j_lt_k
      exact h_not_cond h_cond
    if h_eq : k = j then
      rw [h_eq]
      rfl
    else
      have h_k_lt_j : k < j := Nat.lt_of_le_of_ne h_k_le_j h_eq
      rfl

end DafnySpecs.NpPiecewise