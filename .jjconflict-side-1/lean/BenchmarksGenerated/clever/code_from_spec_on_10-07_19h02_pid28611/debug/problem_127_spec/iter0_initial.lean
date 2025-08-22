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
def hasIntersection (interval1: Int × Int) (interval2: Int × Int) : Bool :=
let (s1, e1) := interval1
let (s2, e2) := interval2
let intersectionStart := max s1 s2
let intersectionEnd := min e1 e2
intersectionStart ≤ intersectionEnd

-- LLM HELPER
def intersectionLength (interval1: Int × Int) (interval2: Int × Int) : Int :=
let (s1, e1) := interval1
let (s2, e2) := interval2
let intersectionStart := max s1 s2
let intersectionEnd := min e1 e2
intersectionEnd - intersectionStart

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

-- LLM HELPER
lemma int_to_nat_nonneg (n : Int) (h : n ≥ 0) : (n.toNat : Int) = n := by
  rw [Int.toNat_of_nonneg h]

-- LLM HELPER
lemma max_min_properties (s1 e1 s2 e2 : Int) :
  let intersectionStart := max s1 s2
  let intersectionEnd := min e1 e2
  intersectionStart ≤ intersectionEnd ↔ max s1 s2 ≤ min e1 e2 := by
  simp

-- LLM HELPER
lemma intersection_length_nonneg (interval1 interval2 : Int × Int) 
  (h : hasIntersection interval1 interval2) :
  intersectionLength interval1 interval2 ≥ 0 := by
  let (s1, e1) := interval1
  let (s2, e2) := interval2
  simp [hasIntersection, intersectionLength] at h ⊢
  linarith

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
    
    simp [implementation]
    
    constructor
    · constructor
      · intro h
        simp at h
        by_cases hInt : hasIntersection
        · simp [hInt] at h
          let length := intersectionEnd - intersectionStart
          have h_nonneg : length ≥ 0 := by
            simp [hasIntersection] at hInt
            linarith
          simp [h_nonneg] at h
          constructor
          · exact hInt
          · simp [isPrime]
            exact h
        · simp [hInt] at h
      · intro ⟨hInt, hPrime⟩
        simp [hInt]
        let length := intersectionEnd - intersectionStart
        have h_nonneg : length ≥ 0 := by
          simp [hasIntersection] at hInt
          linarith
        simp [h_nonneg]
        simp [isPrime] at hPrime
        exact hPrime
    
    constructor
    · constructor
      · intro h
        simp at h
        by_cases hInt : hasIntersection
        · simp [hInt] at h
          let length := intersectionEnd - intersectionStart
          have h_nonneg : length ≥ 0 := by
            simp [hasIntersection] at hInt
            linarith
          simp [h_nonneg] at h
          right
          simp [isPrime]
          exact h
        · left
          exact hInt
      · intro h
        simp
        cases' h with h h
        · simp [h]
        · by_cases hInt : hasIntersection
          · simp [hInt]
            let length := intersectionEnd - intersectionStart
            have h_nonneg : length ≥ 0 := by
              simp [hasIntersection] at hInt
              linarith
            simp [h_nonneg]
            simp [isPrime] at h
            exact h
          · simp [hInt]
    
    · by_cases hInt : hasIntersection
      · simp [implementation, hInt]
        let length := intersectionEnd - intersectionStart
        have h_nonneg : length ≥ 0 := by
          simp [hasIntersection] at hInt
          linarith
        simp [h_nonneg]
        by_cases hPrime : Nat.Prime length.toNat
        · left
          rfl
        · right
          rfl
      · simp [implementation, hInt]
        right
        rfl