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

-- LLM HELPER
lemma max_min_le_iff (a b c d : Int) : max a b ≤ min c d ↔ a ≤ c ∧ a ≤ d ∧ b ≤ c ∧ b ≤ d := by
  constructor
  · intro h
    constructor
    · exact le_trans (le_max_left a b) (le_trans h (min_le_left c d))
    · exact le_trans (le_max_left a b) (le_trans h (min_le_right c d))
    · constructor
      · exact le_trans (le_max_right a b) (le_trans h (min_le_left c d))
      · exact le_trans (le_max_right a b) (le_trans h (min_le_right c d))
  · intro ⟨h1, h2, h3, h4⟩
    exact le_trans (max_le h1 h3) (le_min h2 h4)

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
        · simp at h
          constructor
          · exact h_int
          · exact h_prime.2
        · simp at h
        · simp at h
      · intro ⟨hInt, hPrime⟩
        split_ifs with h_int h_prime
        · simp
        · simp [int_sub_nonneg_iff] at h_prime
          exfalso
          exact h_prime.1 (int_sub_nonneg_iff.mpr hInt)
        · simp at hInt
          exfalso
          exact h_int hInt
    
    constructor
    · constructor
      · intro h
        split_ifs at h with h_int h_prime
        · simp at h
          right
          exact h_prime.2
        · left
          exact h_int
        · left
          exact h_int
      · intro h
        cases' h with h h
        · split_ifs with h_int
          · simp
          · simp
        · split_ifs with h_int h_prime
          · simp at h
            exfalso
            exact h h_prime.2
          · simp
    
    · by_cases h_int : hasIntersection
      · simp only [h_int, true_iff]
        split_ifs with h_prime
        · left
        · right
      · simp only [h_int, false_iff]
        split_ifs
        · left
        · right