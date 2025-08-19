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

def implementation (interval1: Int × Int) (interval2: Int × Int) : String :=
let (s1, e1) := interval1
let (s2, e2) := interval2
let intersectionStart := max s1 s2
let intersectionEnd := min e1 e2
let hasIntersection := intersectionStart ≤ intersectionEnd
let lengthNat := if hasIntersection then (intersectionEnd - intersectionStart).toNat else 0
let isPrime := hasIntersection ∧ Nat.Prime lengthNat
if isPrime then "YES" else "NO"

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
        simp only [ite_eq_left_iff, not_and, not_not] at h
        push_neg at h
        simp at h
        cases' h with h h
        · constructor
          · exact h
          · simp only [lengthNat]
            simp [h]
            exact h.2
        · exfalso
          exact h rfl
      · intro h
        simp only [ite_eq_left_iff, not_and, not_not]
        left
        exact ⟨h.1, by simp [lengthNat, h.1]; exact h.2⟩
    · constructor
      · intro h
        simp only [ite_eq_right_iff, and_imp] at h
        push_neg
        cases' Classical.em hasIntersection with hi hi
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
        cases' h with h h
        · contradiction
        · simp [lengthNat, hi] at h
          exact h hp
    · simp only [ite_eq_left_iff, ite_eq_right_iff]
      tauto