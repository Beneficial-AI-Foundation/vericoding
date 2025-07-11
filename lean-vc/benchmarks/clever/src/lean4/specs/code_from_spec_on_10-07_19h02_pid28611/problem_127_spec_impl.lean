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
  if length ≥ 0 ∧ Nat.Prime length.toNat then "YES" else "NO"
else "NO"

-- LLM HELPER
lemma int_sub_nonneg_iff (a b : Int) : a - b ≥ 0 ↔ b ≤ a := by
  simp [Int.sub_nonneg]

theorem correctness
(interval1: Int × Int)
(interval2: Int × Int)
: problem_spec implementation interval1 interval2 := by
  use implementation interval1 interval2
  constructor
  · rfl
  · intro h1 h2
    let (s1, e1) := interval1
    let (s2, e2) := interval2
    let intersectionStart := max s1 s2
    let intersectionEnd := min e1 e2
    let hasIntersection := intersectionStart ≤ intersectionEnd
    let isPrime := Nat.Prime (intersectionEnd - intersectionStart).toNat
    
    unfold implementation
    simp only [max_def, min_def]
    
    constructor
    · constructor
      · intro h
        split_ifs at h with h_int h_prime
        · simp only [true_iff] at h
          constructor
          · exact h_int
          · exact h_prime.2
        · simp only [true_iff] at h
        · simp only [true_iff] at h
      · intro ⟨hInt, hPrime⟩
        split_ifs with h_int h_prime
        · simp only [true_iff]
        · simp only [int_sub_nonneg_iff] at h_prime
          exfalso
          exact h_prime.1 hInt
        · simp only [true_iff]
          exfalso
          exact h_int hInt
    
    constructor
    · constructor
      · intro h
        split_ifs at h with h_int h_prime
        · simp only [true_iff] at h
          right
          exact h_prime.2
        · left
          exact h_int
        · left
          exact h_int
      · intro h
        cases' h with h h
        · split_ifs with h_int
          · simp only [true_iff]
            exfalso
            exact h h_int
          · simp only [true_iff]
        · split_ifs with h_int h_prime
          · simp only [true_iff]
            exfalso
            exact h h_prime.2
          · simp only [true_iff]
    
    · by_cases h_int : hasIntersection
      · simp only [h_int, true_iff]
        by_cases h_prime : (intersectionEnd - intersectionStart ≥ 0 ∧ Nat.Prime (intersectionEnd - intersectionStart).toNat)
        · simp only [h_prime, if_true]
          left
        · simp only [h_prime, if_false]
          right
      · simp only [h_int, false_iff]
        simp only [h_int, if_false]
        right