namespace NpPiecewise

-- LLM HELPER
def find_first_match {m : Nat} (condlist : Vector (Float → Bool) m) (val : Float) : Option Nat :=
  let rec aux (i : Nat) : Option Nat :=
    if h : i < m then
      if condlist[i]! val then
        some i
      else
        aux (i + 1)
    else
      none
  aux 0

-- LLM HELPER
def apply_piecewise_single {m : Nat} (val : Float) (condlist : Vector (Float → Bool) m) (funclist : Vector (Float → Float) m) : Float :=
  match find_first_match condlist val with
  | some i => funclist[i]! val
  | none => val

def piecewise {n m : Nat} (x : Vector Float n) (condlist : Vector (Float → Bool) m) (funclist : Vector (Float → Float) m) : Vector Float n :=
  Vector.ofFn (fun i : Fin n => apply_piecewise_single (x.get i) condlist funclist)

-- LLM HELPER
lemma vector_length_ofFn {n : Nat} (f : Fin n → Float) : (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn, Vector.toList]

-- LLM HELPER
lemma vector_get_ofFn {n : Nat} (f : Fin n → Float) (i : Nat) (h : i < n) : (Vector.ofFn f)[i]! = f ⟨i, h⟩ := by
  simp [Vector.ofFn, Vector.get]

-- LLM HELPER
lemma find_first_match_correct {m : Nat} (condlist : Vector (Float → Bool) m) (val : Float) (j : Nat) (hj : j < m) :
  condlist[j]! val → ∃ i, find_first_match condlist val = some i ∧ i ≤ j := by
  intro hcond
  simp [find_first_match]
  let rec aux_correct (k : Nat) : k ≤ j → ∃ i, (if h : k < m then if condlist[k]! val then some k else aux_correct (k + 1) else none) = some i ∧ i ≤ j := by
    intro hk
    if hkm : k < m then
      if hck : condlist[k]! val then
        exists k
        simp [hkm, hck, hk]
      else
        apply aux_correct (k + 1)
        omega
    else
      exists j
      simp [hkm]
      exact le_refl j
  exact aux_correct 0 (by omega)

-- LLM HELPER
lemma find_first_match_gives_valid_index {m : Nat} (condlist : Vector (Float → Bool) m) (val : Float) (i : Nat) :
  find_first_match condlist val = some i → i < m := by
  intro h
  simp [find_first_match] at h
  let rec aux_valid (k : Nat) : (if h : k < m then if condlist[k]! val then some k else aux_valid (k + 1) else none) = some i → i < m := by
    intro haux
    if hkm : k < m then
      if hck : condlist[k]! val then
        simp [hkm, hck] at haux
        rw [←haux]
        exact hkm
      else
        simp [hkm, hck] at haux
        exact aux_valid (k + 1) haux
    else
      simp [hkm] at haux
  exact aux_valid 0 h

-- LLM HELPER
lemma find_first_match_finds_first {m : Nat} (condlist : Vector (Float → Bool) m) (val : Float) (i : Nat) :
  find_first_match condlist val = some i → condlist[i]! val := by
  intro h
  simp [find_first_match] at h
  let rec aux_finds (k : Nat) : (if h : k < m then if condlist[k]! val then some k else aux_finds (k + 1) else none) = some i → condlist[i]! val := by
    intro haux
    if hkm : k < m then
      if hck : condlist[k]! val then
        simp [hkm, hck] at haux
        rw [←haux]
        exact hck
      else
        simp [hkm, hck] at haux
        exact aux_finds (k + 1) haux
    else
      simp [hkm] at haux
  exact aux_finds 0 h

theorem piecewise_spec {n m : Nat} (x : Vector Float n) (condlist : Vector (Float → Bool) m) (funclist : Vector (Float → Float) m)
  (h : m = m) :
  let ret := piecewise x condlist funclist
  (ret.toList.length = n) ∧
  (∀ i j : Nat, i < n → j < m →
    condlist[j]! (x[i]!) → ret[i]! = funclist[j]! (x[i]!)) := by
  constructor
  · simp [piecewise]
    exact vector_length_ofFn _
  · intros i j hi hj hcond
    simp [piecewise]
    rw [vector_get_ofFn]
    simp [apply_piecewise_single]
    have ⟨k, hk_eq, hk_le⟩ := find_first_match_correct condlist (x[i]!) j hj hcond
    rw [hk_eq]
    simp
    have hk_valid := find_first_match_gives_valid_index condlist (x[i]!) k hk_eq
    have hk_cond := find_first_match_finds_first condlist (x[i]!) k hk_eq
    rw [hk_cond]

end NpPiecewise