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
def gcd (a b : Nat) : Nat :=
if b = 0 then a else gcd b (a % b)

-- LLM HELPER
def lcm (a b : Nat) : Nat :=
if a = 0 ∨ b = 0 then 0 else (a * b) / gcd a b

def implementation (x: String) (n: String) : Bool :=
let fx := x.splitOn "/"
let fn := n.splitOn "/"
if fx.length = 2 ∧ fn.length = 2 ∧ fx.all String.isNat ∧ fn.all String.isNat then
  let p1 := fx[0]!.toNat!
  let q1 := fx[1]!.toNat!
  let p2 := fn[0]!.toNat!
  let q2 := fn[1]!.toNat!
  if q1 ≠ 0 ∧ q2 ≠ 0 then
    (q1 * q2) % (p1 * p2) = 0
  else
    false
else
  false

theorem correctness
(x: String) (n: String)
: problem_spec implementation x n := by
  unfold problem_spec
  let fx := x.splitOn "/"
  let fn := n.splitOn "/"
  let result := implementation x n
  use result
  constructor
  · rfl
  · intro h1 h2 h3 h4 h5 h6
    unfold implementation
    simp only [fx, fn]
    split_ifs with h
    · cases' h with h7 h8
      cases' h7 with h9 h10
      cases' h8 with h11 h12
      simp at h9 h10 h11 h12
      split_ifs with h17
      · cases' h17 with h18 h19
        let p1 := fx[0]!.toNat!
        let q1 := fx[1]!.toNat!
        let p2 := fn[0]!.toNat!
        let q2 := fn[1]!.toNat!
        constructor
        · intro h20
          obtain ⟨k, hk⟩ := h20
          have : k * p1 * p2 = q1 * q2 := hk
          rw [Nat.mul_assoc] at this
          have : (q1 * q2) % (p1 * p2) = 0 := by
            rw [←this]
            simp [Nat.mul_mod]
          exact this
        · intro h20
          use (q1 * q2) / (p1 * p2)
          have hp : p1 * p2 > 0 := by
            apply Nat.mul_pos
            · by_cases hp1 : p1 = 0
              · simp [hp1] at h20
                exact Nat.pos_of_ne_zero h18
              · exact Nat.pos_of_ne_zero hp1
            · by_cases hp2 : p2 = 0
              · simp [hp2] at h20
                exact Nat.pos_of_ne_zero h19
              · exact Nat.pos_of_ne_zero hp2
          have hdiv : (p1 * p2) ∣ (q1 * q2) := by
            rw [Nat.dvd_iff_mod_eq_zero]
            exact h20
          rw [Nat.mul_div_cancel' hdiv]
          simp [Nat.mul_assoc]
      · exfalso
        exact h17 ⟨h5, h6⟩
    · exfalso
      exact h ⟨⟨h1, h2⟩, h3, h4⟩