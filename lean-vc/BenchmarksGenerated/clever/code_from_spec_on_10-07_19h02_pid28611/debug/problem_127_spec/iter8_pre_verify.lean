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
    
    constructor
    · constructor
      · intro h
        simp only [max_def, min_def] at h ⊢
        split_ifs at h with h_int h_prime
        · simp at h
          constructor
          · exact h_int
          · exact h_prime.2
        · simp at h
        · simp at h
      · intro ⟨hInt, hPrime⟩
        simp only [max_def, min_def]
        split_ifs with h_int h_prime
        · simp
        · simp [int_sub_nonneg_iff] at h_prime
          contradiction
        · simp at hInt
          contradiction
    
    constructor
    · constructor
      · intro h
        simp only [max_def, min_def] at h ⊢
        split_ifs at h with h_int h_prime
        · simp at h
          right
          exact h_prime.2
        · left
          exact h_int
        · left
          exact h_int
      · intro h
        simp only [max_def, min_def]
        cases' h with h h
        · split_ifs with h_int
          · simp
          · simp
        · split_ifs with h_int h_prime
          · simp at h
            contradiction
          · simp
    
    · simp only [or_comm]
      by_cases h_int : intersectionStart ≤ intersectionEnd
      · simp only [max_def, min_def] at h_int ⊢
        split_ifs with h_int'
        · simp
        · simp
      · simp only [max_def, min_def] at h_int ⊢
        split_ifs with h_int'
        · simp
        · simp