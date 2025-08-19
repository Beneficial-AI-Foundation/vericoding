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
    let l := lcm (p1 * p2) (q1 * q2)
    l % (p1 * p2) = 0 ∧ l % (q1 * q2) = 0 ∧ l = q1 * q2
  else
    false
else
  false

-- LLM HELPER
lemma lcm_dvd_iff (a b c : Nat) (ha : a ≠ 0) (hb : b ≠ 0) : 
  lcm a b = c ↔ (a ∣ c ∧ b ∣ c ∧ ∀ d, a ∣ d → b ∣ d → c ∣ d) := by
  sorry

-- LLM HELPER
lemma dvd_iff_mod_eq_zero (a b : Nat) : a ∣ b ↔ b % a = 0 := by
  sorry

-- LLM HELPER  
lemma exists_k_iff_lcm_eq (p1 q1 p2 q2 : Nat) (hq1 : q1 ≠ 0) (hq2 : q2 ≠ 0) :
  (∃ k, k * p1 * p2 = q1 * q2) ↔ lcm (p1 * p2) (q1 * q2) = q1 * q2 := by
  sorry

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
      have h13 : fx.length = 2 := by simp [fx]; exact h1
      have h14 : fn.length = 2 := by simp [fn]; exact h2
      have h15 : fx.all String.isNat := by simp [fx]; exact h3
      have h16 : fn.all String.isNat := by simp [fn]; exact h4
      split_ifs with h17
      · cases' h17 with h18 h19
        let p1 := fx[0]!.toNat!
        let q1 := fx[1]!.toNat!
        let p2 := fn[0]!.toNat!
        let q2 := fn[1]!.toNat!
        have hq1 : q1 ≠ 0 := h18
        have hq2 : q2 ≠ 0 := h19
        rw [exists_k_iff_lcm_eq p1 q1 p2 q2 hq1 hq2]
        simp only [lcm]
        constructor
        · intro h20
          cases' h20 with h21 h22
          cases' h21 with h23 h24
          exact h24
        · intro h20
          constructor
          · rw [dvd_iff_mod_eq_zero]
            simp [h20]
          · constructor
            · rw [dvd_iff_mod_eq_zero]
              simp [h20]
            · exact h20
      · exfalso
        exact h17 ⟨h5, h6⟩
    · exfalso
      exact h ⟨⟨h1, h2⟩, h3, h4⟩