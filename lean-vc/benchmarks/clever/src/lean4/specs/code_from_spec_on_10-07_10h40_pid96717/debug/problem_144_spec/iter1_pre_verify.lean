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
def gcd_nat (a b : Nat) : Nat :=
if b = 0 then a else gcd_nat b (a % b)

-- LLM HELPER
def lcm_nat (a b : Nat) : Nat :=
if a = 0 ∨ b = 0 then 0 else (a * b) / gcd_nat a b

def implementation (x: String) (n: String) : Bool :=
let fx := x.splitOn "/"
let fn := n.splitOn "/"
if fx.length = 2 ∧ fn.length = 2 ∧ fx.all String.isNat ∧ fn.all String.isNat then
  let p1 := fx[0]!.toNat!
  let q1 := fx[1]!.toNat!
  let p2 := fn[0]!.toNat!
  let q2 := fn[1]!.toNat!
  if q1 ≠ 0 ∧ q2 ≠ 0 then
    let lcm := lcm_nat (p1 * p2) (q1 * q2)
    lcm ≠ 0 ∧ lcm % (p1 * p2) = 0 ∧ lcm % (q1 * q2) = 0
  else
    false
else
  false

-- LLM HELPER
lemma gcd_nat_spec (a b : Nat) : gcd_nat a b = Nat.gcd a b := by
  sorry

-- LLM HELPER
lemma lcm_nat_spec (a b : Nat) : lcm_nat a b = Nat.lcm a b := by
  sorry

-- LLM HELPER
lemma exists_k_iff_lcm (p1 q1 p2 q2 : Nat) (hq1 : q1 ≠ 0) (hq2 : q2 ≠ 0) :
  (∃ k, k * p1 * p2 = q1 * q2) ↔ 
  (let lcm := lcm_nat (p1 * p2) (q1 * q2); lcm ≠ 0 ∧ lcm % (p1 * p2) = 0 ∧ lcm % (q1 * q2) = 0) := by
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
    · obtain ⟨hlen1, hlen2, hnat1, hnat2⟩ := h
      simp only [hlen1, hlen2, hnat1, hnat2, true_and]
      split_ifs with hq
      · obtain ⟨hq1, hq2⟩ := hq
        have hq1' : fx[1]!.toNat! ≠ 0 := by
          rw [← hlen1] at h2
          exact hq1
        have hq2' : fn[1]!.toNat! ≠ 0 := by
          rw [← hlen2] at h2
          exact hq2
        apply exists_k_iff_lcm
        · exact hq1'
        · exact hq2'
      · exfalso
        exact hq ⟨h5, h6⟩
    · exfalso
      exact h ⟨h1, h2, h3, h4⟩