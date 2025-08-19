import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
instance : DecidableEq Float := Classical.choose_spec ⟨fun a b => Classical.prop_decidable (a = b)⟩

-- LLM HELPER
instance (P : Float → Prop) : Decidable (P x) := Classical.prop_decidable (P x)

-- LLM HELPER
def findLastNonZero {n : Nat} (seq : Vector Float n) : Option (Fin n) :=
  if n = 0 then none
  else
    let rec loop (i : Nat) (h : i < n) : Option (Fin n) :=
      if h_neq : seq.get ⟨n - 1 - i, by 
        have : i < n := h
        have : n > 0 := Nat.pos_of_ne_zero (by 
          intro h_eq
          rw [h_eq] at h
          exact Nat.lt_irrefl 0 h)
        simp [Nat.sub_sub, Nat.add_comm]
        exact Nat.sub_lt_self (by omega) (by omega)⟩ ≠ 0 then
        some ⟨n - 1 - i, by 
          have : i < n := h
          have : n > 0 := Nat.pos_of_ne_zero (by 
            intro h_eq
            rw [h_eq] at h
            exact Nat.lt_irrefl 0 h)
          simp [Nat.sub_sub, Nat.add_comm]
          exact Nat.sub_lt_self (by omega) (by omega)⟩
      else if h_lt : i + 1 < n then
        loop (i + 1) (by omega)
      else
        none
    loop 0 (by 
      intro h_eq
      rw [h_eq]
      exact Nat.pos_of_ne_zero (by 
        intro h_zero
        rw [h_zero] at h_eq
        exact absurd h_eq rfl))

-- LLM HELPER
def trimAtPosition {n : Nat} (seq : Vector Float n) (pos : Option (Fin n)) : Vector Float n :=
  match pos with
  | none => seq  -- All zeros, return as is
  | some k => 
    Vector.ofFn (fun i => if i.val ≤ k.val then seq.get i else 0)

/-- Remove trailing zeros from a sequence of polynomial coefficients.
    Returns the sequence with trailing zeros removed. If the sequence would be empty 
    after trimming, returns the first element. Empty sequences are handled. -/
def trimseq {n : Nat} (seq : Vector Float n) : Id (Vector Float n) :=
  if n = 0 then pure seq
  else if h_neq : seq.get ⟨n - 1, by 
    have : n > 0 := Nat.pos_of_ne_zero (by 
      intro h_eq
      rw [h_eq]
      exact Nat.lt_irrefl 0 (by omega))
    exact Nat.sub_lt (by omega) (by omega)⟩ ≠ 0 then pure seq
  else
    let lastNonZero := findLastNonZero seq
    pure (trimAtPosition seq lastNonZero)

-- LLM HELPER
lemma findLastNonZero_spec {n : Nat} (seq : Vector Float n) :
  match findLastNonZero seq with
  | none => n > 0 → ∀ i : Fin n, seq.get i = 0
  | some k => seq.get k ≠ 0 ∧ ∀ j : Fin n, j.val > k.val → seq.get j = 0 := by
  unfold findLastNonZero
  split
  · simp
  · simp only [Option.some.injEq]
    have : n > 0 := by omega
    let rec loop_spec (i : Nat) (h : i < n) : 
      match (let rec loop (i : Nat) (h : i < n) : Option (Fin n) :=
        if h_neq : seq.get ⟨n - 1 - i, by 
          have : i < n := h
          have : n > 0 := Nat.pos_of_ne_zero (by 
            intro h_eq
            rw [h_eq] at h
            exact Nat.lt_irrefl 0 h)
          simp [Nat.sub_sub, Nat.add_comm]
          exact Nat.sub_lt_self (by omega) (by omega)⟩ ≠ 0 then
          some ⟨n - 1 - i, by 
            have : i < n := h
            have : n > 0 := Nat.pos_of_ne_zero (by 
              intro h_eq
              rw [h_eq] at h
              exact Nat.lt_irrefl 0 h)
            simp [Nat.sub_sub, Nat.add_comm]
            exact Nat.sub_lt_self (by omega) (by omega)⟩
        else if h_lt : i + 1 < n then
          loop (i + 1) (by omega)
        else
          none
        loop) i h with
      | none => ∀ j : Fin n, j.val ≥ n - 1 - i → seq.get j = 0
      | some k => seq.get k ≠ 0 ∧ ∀ j : Fin n, j.val > k.val → seq.get j = 0 := by
      induction i using Nat.strong_induction_on generalizing h
      case ind i ih =>
        simp only [findLastNonZero.loop]
        split
        · constructor
          · assumption
          · intro j hj
            by_cases h_eq : j.val = n - 1 - i
            · simp [h_eq]; assumption
            · have : j.val > n - 1 - i := by omega
              simp
        · split
          · apply ih
            · omega
            · omega
          · intro j hj
            simp
    exact loop_spec 0 (by 
      intro h_eq
      rw [h_eq]
      exact Nat.pos_of_ne_zero (by 
        intro h_zero
        rw [h_zero] at h_eq
        exact absurd h_eq rfl))

-- LLM HELPER
lemma trimAtPosition_spec {n : Nat} (seq : Vector Float n) (pos : Option (Fin n)) :
  let result := trimAtPosition seq pos
  match pos with
  | none => result = seq
  | some k => 
    (∀ i : Fin n, i.val ≤ k.val → result.get i = seq.get i) ∧
    (∀ i : Fin n, i.val > k.val → result.get i = 0) := by
  unfold trimAtPosition
  split
  · simp
  · constructor
    · intro i hi
      simp [Vector.get_ofFn]
      simp [hi]
    · intro i hi  
      simp [Vector.get_ofFn]
      simp [hi]

-- LLM HELPER
lemma nat_pos_of_ne_zero {n : Nat} (h : n ≠ 0) : n > 0 := Nat.pos_of_ne_zero h

-- LLM HELPER
lemma one_le_of_pos {n : Nat} (h : n > 0) : 1 ≤ n := h

-- LLM HELPER
lemma sub_lt_of_pos {n : Nat} (h : n > 0) : n - 1 < n := Nat.sub_lt h (by omega)

/-- Specification: trimseq removes trailing zeros while preserving at least one element.
    For non-empty sequences, if the last element is non-zero, return the sequence unchanged.
    If the last element is zero, trim trailing zeros but always keep at least one element. -/
theorem trimseq_spec {n : Nat} (seq : Vector Float n) :
    ⦃⌜True⌝⦄
    trimseq seq
    ⦃⇓result => ⌜result.toList.length = n ∧
                 (n = 0 ∨ (n > 0 ∧ seq.get ⟨n - 1, Nat.sub_lt (nat_pos_of_ne_zero (by 
                   intro h_eq
                   rw [h_eq]
                   exact Nat.lt_irrefl 0 (by omega))) (by omega)⟩ ≠ 0) → result = seq) ∧
                 (n > 0 ∧ seq.get ⟨n - 1, Nat.sub_lt (nat_pos_of_ne_zero (by 
                   intro h_eq
                   rw [h_eq]
                   exact Nat.lt_irrefl 0 (by omega))) (by omega)⟩ = 0 → 
                   (∃ k : Fin n, 
                    (∀ j : Fin n, j.val > k.val → seq.get j = 0) ∧
                    (∀ i : Fin n, i.val ≤ k.val → result.get i = seq.get i) ∧
                    (∀ i : Fin n, i.val > k.val → result.get i = 0) ∧
                    (k.val > 0 → seq.get k ≠ 0)))⌝⦄ := by
  unfold trimseq
  simp only [Triple.mk_bind_mk, Triple.mk_pure]
  constructor
  · simp
  · constructor
    · simp [Vector.toList_length]
    · constructor
      · intro h
        cases h with
        | inl h_empty => 
          simp [h_empty]
        | inr h_nonzero =>
          simp only [h_nonzero.1]
          split
          · simp
          · simp [h_nonzero.2]
          · simp [h_nonzero.2]
      · intro h
        simp only [h.1]
        split
        · contradiction
        · simp [h.2]
        · have last_zero : seq.get ⟨n - 1, Nat.sub_lt (nat_pos_of_ne_zero (by 
            intro h_eq
            rw [h_eq] at h
            exact Nat.lt_irrefl 0 h.1)) (by omega)⟩ = 0 := h.2
          have pos_spec := findLastNonZero_spec seq
          have trim_spec := trimAtPosition_spec seq (findLastNonZero seq)
          cases h_find : findLastNonZero seq with
          | none => 
            simp [h_find] at pos_spec trim_spec
            use ⟨0, by omega⟩
            constructor
            · intro j hj
              apply pos_spec h.1
            · simp [trim_spec]
              constructor
              · intro i hi
                simp [Vector.get_ofFn]
              · constructor
                · intro i hi
                  simp [Vector.get_ofFn]
                  simp [hi]
                · intro hk
                  apply pos_spec h.1
          | some k =>
            simp [h_find] at pos_spec trim_spec
            use k
            constructor
            · exact pos_spec.2
            · constructor
              · exact trim_spec.1
              · constructor
                · exact trim_spec.2
                · intro hk
                  exact pos_spec.1