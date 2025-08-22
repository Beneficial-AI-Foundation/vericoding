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
if hasIntersection then
  let length := intersectionEnd - intersectionStart
  if length ≥ 0 then
    if Nat.Prime length.toNat then "YES" else "NO"
  else "NO"
else "NO"

theorem correctness
(interval1: Int × Int)
(interval2: Int × Int)
: problem_spec implementation interval1 interval2 := by
  let (s1, e1) := interval1
  let (s2, e2) := interval2
  use implementation interval1 interval2
  constructor
  · rfl
  · intro h1 h2
    let intersectionStart := max s1 s2
    let intersectionEnd := min e1 e2
    let hasIntersection := intersectionStart ≤ intersectionEnd
    let isPrime := Nat.Prime (intersectionEnd - intersectionStart).toNat
    
    unfold implementation
    
    constructor
    · constructor
      · intro h
        by_cases hInt : hasIntersection
        · simp [hInt] at h
          let length := intersectionEnd - intersectionStart
          have h_nonneg : length ≥ 0 := by
            unfold hasIntersection at hInt
            linarith
          simp [h_nonneg] at h
          constructor
          · exact hInt
          · unfold isPrime
            exact h
        · simp [hInt] at h
      · intro ⟨hInt, hPrime⟩
        simp [hInt]
        let length := intersectionEnd - intersectionStart
        have h_nonneg : length ≥ 0 := by
          unfold hasIntersection at hInt
          linarith
        simp [h_nonneg]
        unfold isPrime at hPrime
        exact hPrime
    
    constructor
    · constructor
      · intro h
        by_cases hInt : hasIntersection
        · simp [hInt] at h
          let length := intersectionEnd - intersectionStart
          have h_nonneg : length ≥ 0 := by
            unfold hasIntersection at hInt
            linarith
          simp [h_nonneg] at h
          right
          unfold isPrime
          exact h
        · left
          exact hInt
      · intro h
        cases' h with h h
        · simp [h]
        · by_cases hInt : hasIntersection
          · simp [hInt]
            let length := intersectionEnd - intersectionStart
            have h_nonneg : length ≥ 0 := by
              unfold hasIntersection at hInt
              linarith
            simp [h_nonneg]
            unfold isPrime at h
            exact h
          · simp [hInt]
    
    · by_cases hInt : hasIntersection
      · simp [hInt]
        let length := intersectionEnd - intersectionStart
        have h_nonneg : length ≥ 0 := by
          unfold hasIntersection at hInt
          linarith
        simp [h_nonneg]
        by_cases hPrime : Nat.Prime length.toNat
        · left
          rfl
        · right
          rfl
      · simp [hInt]
        right
        rfl