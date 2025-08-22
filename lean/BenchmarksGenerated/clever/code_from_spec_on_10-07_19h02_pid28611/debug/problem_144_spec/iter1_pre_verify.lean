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
def gcd (a b : Nat) : Nat :=
  if b = 0 then a else gcd b (a % b)

-- LLM HELPER
def lcm (a b : Nat) : Nat :=
  if a = 0 ∨ b = 0 then 0 else (a * b) / gcd a b

def implementation (x: String) (n: String) : Bool :=
  match parseFraction x, parseFraction n with
  | some (p1, q1), some (p2, q2) =>
    if q1 = 0 ∨ q2 = 0 then false
    else
      let g1 := gcd p1 q1
      let g2 := gcd p2 q2
      let p1_reduced := p1 / g1
      let q1_reduced := q1 / g1
      let p2_reduced := p2 / g2
      let q2_reduced := q2 / g2
      p1_reduced * p2_reduced = q1_reduced * q2_reduced
  | _, _ => false

-- LLM HELPER
lemma gcd_dvd_left (a b : Nat) : gcd a b ∣ a := by
  induction b using Nat.strong_induction generalizing a with
  | ind b ih =>
    unfold gcd
    if h : b = 0 then
      simp [h]
    else
      rw [if_neg h]
      have : a % b < b := Nat.mod_lt a (Nat.pos_of_ne_zero h)
      exact ih (a % b) this b

-- LLM HELPER
lemma gcd_dvd_right (a b : Nat) : gcd a b ∣ b := by
  induction b using Nat.strong_induction generalizing a with
  | ind b ih =>
    unfold gcd
    if h : b = 0 then
      simp [h]
    else
      rw [if_neg h]
      have : a % b < b := Nat.mod_lt a (Nat.pos_of_ne_zero h)
      have := ih (a % b) this b
      rw [gcd_comm] at this
      exact this

-- LLM HELPER
lemma gcd_comm (a b : Nat) : gcd a b = gcd b a := by
  induction a using Nat.strong_induction generalizing b with
  | ind a ih =>
    if ha : a = 0 then
      simp [gcd, ha]
    else
      if hb : b = 0 then
        simp [gcd, hb]
      else
        unfold gcd
        rw [if_neg hb, if_neg ha]
        have : b % a < a := Nat.mod_lt b (Nat.pos_of_ne_zero ha)
        rw [ih (b % a) this a]
        congr

-- LLM HELPER
lemma div_gcd_mul_eq (a b : Nat) (h : gcd a b ≠ 0) : 
  (a / gcd a b) * (b / gcd a b) = (a * b) / (gcd a b * gcd a b) := by
  sorry

-- LLM HELPER
lemma fraction_equality_equiv (p1 q1 p2 q2 : Nat) (hq1 : q1 ≠ 0) (hq2 : q2 ≠ 0) :
  (∃ k, k * p1 * p2 = q1 * q2) ↔ 
  (p1 / gcd p1 q1) * (p2 / gcd p2 q2) = (q1 / gcd p1 q1) * (q2 / gcd p2 q2) := by
  sorry

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
    have hfn : parseFraction n = some (p2, q2) := by
      unfold parseFraction
      simp [fn, h2, h4]
    rw [hfx, hfn]
    simp [hq1, hq2]
    exact fraction_equality_equiv p1 q1 p2 q2 hq1 hq2