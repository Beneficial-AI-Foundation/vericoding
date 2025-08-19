import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: Int × Int → Int × Int → String)
(interval1: Int × Int)
(interval2: Int × Int) :=
let spec (result: String) :=
let (s1, e1) := interval1;
let (s2, e2) := interval2;
s1 ≤ e1 → s2 ≤ e2 →
let intersectionStart := max s1 s2;
let intersectionEnd := min e1 e2;
let hasIntersection := intersectionStart ≤ intersectionEnd;
let isPrime := Nat.Prime (intersectionEnd - intersectionStart).toNat;
(result = "YES" ↔ hasIntersection ∧ isPrime) ∧
(result = "NO" ↔ ¬hasIntersection ∨ ¬isPrime) ∧
(result = "YES" ∨ result = "NO")
∃ result, implementation interval1 interval2 = result ∧
spec result

-- LLM HELPER
def Nat.Prime (n : Nat) : Prop :=
  n > 1 ∧ ∀ m : Nat, m ∣ n → m = 1 ∨ m = n

def implementation (interval1: Int × Int) (interval2: Int × Int) : String :=
let (s1, e1) := interval1
let (s2, e2) := interval2
let intersectionStart := max s1 s2
let intersectionEnd := min e1 e2
let hasIntersection := intersectionStart ≤ intersectionEnd
let lengthNat := if hasIntersection then (intersectionEnd - intersectionStart).toNat else 0
let isPrime := hasIntersection ∧ Nat.Prime lengthNat
if isPrime then "YES" else "NO"

-- LLM HELPER
lemma int_to_nat_nonneg (a b : Int) (h : a ≤ b) : 0 ≤ b - a := by
  linarith

-- LLM HELPER
lemma to_nat_sub (a b : Int) (h : a ≤ b) : (b - a).toNat = Int.natAbs (b - a) := by
  rw [Int.toNat_of_nonneg (int_to_nat_nonneg a b h)]

theorem correctness
(interval1: Int × Int)
(interval2: Int × Int)
: problem_spec implementation interval1 interval2 := by
  unfold problem_spec
  use implementation interval1 interval2
  constructor
  · rfl
  · unfold implementation
    simp only [and_imp]
    intro h1 h2
    let (s1, e1) := interval1
    let (s2, e2) := interval2
    let intersectionStart := max s1 s2
    let intersectionEnd := min e1 e2
    let hasIntersection := intersectionStart ≤ intersectionEnd
    let lengthNat := if hasIntersection then (intersectionEnd - intersectionStart).toNat else 0
    let isPrime := hasIntersection ∧ Nat.Prime lengthNat
    constructor
    · constructor
      · intro h
        split_ifs at h
        · simp at h
          constructor
          · assumption
          · simp only [lengthNat]
            simp [*]
            assumption
        · simp at h
      · intro h
        simp only [ite_eq_left_iff, not_and, not_not]
        left
        exact ⟨h.1, by simp [lengthNat, h.1]; exact h.2⟩
    · constructor
      · intro h
        simp only [ite_eq_right_iff, and_imp] at h
        by_cases hi : hasIntersection
        · right
          simp [lengthNat, hi]
          intro hp
          have : lengthNat = (intersectionEnd - intersectionStart).toNat := by
            simp [lengthNat, hi]
          rw [this] at hp
          exact h hi hp
        · left
          exact hi
      · intro h
        simp only [ite_eq_right_iff, and_imp]
        intro hi hp
        cases h with
        | inl h => contradiction
        | inr h => 
          simp [lengthNat, hi] at h
          exact h hp
    · by_cases h : isPrime
      · left; simp [h]
      · right; simp [h]