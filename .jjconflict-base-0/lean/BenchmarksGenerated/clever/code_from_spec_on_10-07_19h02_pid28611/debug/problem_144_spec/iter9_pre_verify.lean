import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: String → String → Bool)
(x: String) (n: String) :=
let spec (result: Bool) :=
let fx := x.splitOn "/";
let fn := n.splitOn "/";
fx.length = 2 → fn.length = 2 →
fx.all String.isNat → fn.all String.isNat →
let p1 := fx[0]!.toNat!;
let q1 := fx[1]!.toNat!;
let p2 := fn[0]!.toNat!;
let q2 := fn[1]!.toNat!;
q1 ≠ 0 → q2 ≠ 0 →
(result ↔ (∃ k, k * p1 * p2 = q1 * q2))
∃ result, implementation x n = result ∧
spec result

-- LLM HELPER
def parseFraction (s: String) : Option (Nat × Nat) :=
  let parts := s.splitOn "/"
  if parts.length = 2 ∧ parts.all String.isNat then
    some (parts[0]!.toNat!, parts[1]!.toNat!)
  else
    none

-- LLM HELPER
def myGcd (a b : Nat) : Nat :=
  if b = 0 then a else myGcd b (a % b)
termination_by b
decreasing_by simp_wf; exact Nat.mod_lt a (Nat.pos_of_ne_zero ‹¬b = 0›)

def implementation (x: String) (n: String) : Bool :=
  match parseFraction x, parseFraction n with
  | some (p1, q1), some (p2, q2) =>
    if q1 = 0 ∨ q2 = 0 then false
    else
      let g1 := myGcd p1 q1
      let g2 := myGcd p2 q2
      let p1_reduced := p1 / g1
      let q1_reduced := q1 / g1
      let p2_reduced := p2 / g2
      let q2_reduced := q2 / g2
      p1_reduced * p2_reduced = q1_reduced * q2_reduced
  | _, _ => false

-- LLM HELPER
lemma myGcd_dvd_left (a b : Nat) : myGcd a b ∣ a := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
    unfold myGcd
    if h : b = 0 then
      simp [h]
      exact dvd_refl a
    else
      rw [if_neg h]
      have this : a % b < b := Nat.mod_lt a (Nat.pos_of_ne_zero h)
      have h1 := ih (a % b) this b
      have h2 := myGcd_dvd_right b (a % b)
      exact Nat.dvd_add_iff_left h2 |>.mpr (Nat.dvd_of_mod_eq_zero rfl)

-- LLM HELPER
lemma myGcd_dvd_right (a b : Nat) : myGcd a b ∣ b := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
    unfold myGcd
    if h : b = 0 then
      simp [h]
    else
      rw [if_neg h]
      have this : a % b < b := Nat.mod_lt a (Nat.pos_of_ne_zero h)
      have h1 := ih (a % b) this b
      exact h1

-- LLM HELPER
lemma myGcd_comm (a b : Nat) : myGcd a b = myGcd b a := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    if ha : a = 0 then
      simp [myGcd, ha]
      if hb : b = 0 then
        simp [myGcd, hb]
      else
        simp [myGcd, hb]
    else
      if hb : b = 0 then
        simp [myGcd, hb, ha]
      else
        unfold myGcd
        rw [if_neg hb, if_neg ha]
        have this : b % a < a := Nat.mod_lt b (Nat.pos_of_ne_zero ha)
        rw [ih (b % a) this a]
        congr 1

-- LLM HELPER
lemma fraction_equality_equiv (p1 q1 p2 q2 : Nat) (hq1 : q1 ≠ 0) (hq2 : q2 ≠ 0) :
  (∃ k, k * p1 * p2 = q1 * q2) ↔ 
  (p1 / myGcd p1 q1) * (p2 / myGcd p2 q2) = (q1 / myGcd p1 q1) * (q2 / myGcd p2 q2) := by
  constructor
  · intro ⟨k, hk⟩
    have h1 : myGcd p1 q1 ∣ p1 := myGcd_dvd_left p1 q1
    have h2 : myGcd p1 q1 ∣ q1 := myGcd_dvd_right p1 q1
    have h3 : myGcd p2 q2 ∣ p2 := myGcd_dvd_left p2 q2
    have h4 : myGcd p2 q2 ∣ q2 := myGcd_dvd_right p2 q2
    cases' h1 with a1 ha1
    cases' h2 with b1 hb1
    cases' h3 with a2 ha2
    cases' h4 with b2 hb2
    rw [ha1, hb1, ha2, hb2]
    simp [Nat.mul_div_cancel]
    rw [←ha1, ←hb1, ←ha2, ←hb2] at hk
    have : k * (myGcd p1 q1 * a1) * (myGcd p2 q2 * a2) = (myGcd p1 q1 * b1) * (myGcd p2 q2 * b2) := hk
    ring_nf at this
    have : k * a1 * a2 = b1 * b2 := by
      have : myGcd p1 q1 * myGcd p2 q2 ≠ 0 := by
        simp [Nat.mul_ne_zero_iff]
        constructor
        · cases' Nat.eq_zero_or_pos (myGcd p1 q1) with h h
          · rw [h] at hb1
            simp at hb1
            rw [hb1] at hq1
            contradiction
          · exact Nat.ne_of_gt h
        · cases' Nat.eq_zero_or_pos (myGcd p2 q2) with h h
          · rw [h] at hb2
            simp at hb2
            rw [hb2] at hq2
            contradiction
          · exact Nat.ne_of_gt h
      exact Nat.eq_div_of_mul_eq_left this this
    exact this
  · intro h
    use 1
    ring_nf
    have h1 : myGcd p1 q1 ∣ p1 := myGcd_dvd_left p1 q1
    have h2 : myGcd p1 q1 ∣ q1 := myGcd_dvd_right p1 q1
    have h3 : myGcd p2 q2 ∣ p2 := myGcd_dvd_left p2 q2
    have h4 : myGcd p2 q2 ∣ q2 := myGcd_dvd_right p2 q2
    cases' h1 with a1 ha1
    cases' h2 with b1 hb1
    cases' h3 with a2 ha2
    cases' h4 with b2 hb2
    rw [ha1, hb1, ha2, hb2]
    simp [Nat.mul_div_cancel] at h
    rw [←ha1, ←hb1, ←ha2, ←hb2]
    ring_nf
    have : a1 * a2 = b1 * b2 := h
    rw [this]
    ring

theorem correctness
(x: String) (n: String)
: problem_spec implementation x n := by
  unfold problem_spec
  let fx := x.splitOn "/"
  let fn := n.splitOn "/"
  use implementation x n
  constructor
  · rfl
  · intro h1 h2 h3 h4
    let p1 := fx[0]!.toNat!
    let q1 := fx[1]!.toNat!
    let p2 := fn[0]!.toNat!
    let q2 := fn[1]!.toNat!
    intro hq1 hq2
    unfold implementation
    have hfx : parseFraction x = some (p1, q1) := by
      unfold parseFraction
      simp [fx, h1, h3]
      constructor
      · rfl
      · rfl
    have hfn : parseFraction n = some (p2, q2) := by
      unfold parseFraction
      simp [fn, h2, h4]
      constructor
      · rfl
      · rfl
    rw [hfx, hfn]
    simp [hq1, hq2]
    exact fraction_equality_equiv p1 q1 p2 q2 hq1 hq2