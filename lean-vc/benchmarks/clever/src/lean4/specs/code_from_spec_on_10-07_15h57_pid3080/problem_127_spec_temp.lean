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
let length := intersectionEnd - intersectionStart
let isPrime := if length ≥ 0 then Nat.Prime length.toNat else false
if hasIntersection ∧ isPrime then "YES" else "NO"

-- LLM HELPER
lemma int_to_nat_nonneg (n : Int) (h : n ≥ 0) : (n.toNat : Int) = n := by
  rw [Int.toNat_of_nonneg h]

-- LLM HELPER
lemma intersection_length_nonneg (s1 e1 s2 e2 : Int) (h : max s1 s2 ≤ min e1 e2) : 
  min e1 e2 - max s1 s2 ≥ 0 := by
  linarith

theorem correctness
(interval1: Int × Int)
(interval2: Int × Int)
: problem_spec implementation interval1 interval2 := by
  simp [problem_spec]
  use implementation interval1 interval2
  constructor
  · rfl
  · intro result
    simp [implementation]
    let (s1, e1) := interval1
    let (s2, e2) := interval2
    intros h1 h2
    let intersectionStart := max s1 s2
    let intersectionEnd := min e1 e2
    let hasIntersection := intersectionStart ≤ intersectionEnd
    let length := intersectionEnd - intersectionStart
    let isPrime := if length ≥ 0 then Nat.Prime length.toNat else false
    
    constructor
    · constructor
      · intro h
        simp at h
        split_ifs at h with h_cond h_prime
        · exact ⟨h_cond, h_prime⟩
        · contradiction
      · intro ⟨h_int, h_prime⟩
        simp
        split_ifs with h_cond h_prime_check
        · rfl
        · have : length ≥ 0 := intersection_length_nonneg s1 e1 s2 e2 h_int
          simp [this] at h_prime_check
          contradiction
    
    constructor
    · constructor
      · intro h
        simp at h
        split_ifs at h with h_cond h_prime
        · contradiction
        · by_cases h_neg : length ≥ 0
          · simp [h_neg] at h_prime
            right
            exact h_prime
          · left
            linarith
      · intro h
        simp
        split_ifs with h_cond h_prime_check
        · cases h with
          | inl h_no_int => contradiction
          | inr h_not_prime => 
            have : length ≥ 0 := intersection_length_nonneg s1 e1 s2 e2 h_cond
            simp [this] at h_prime_check
            contradiction
        · rfl
    
    · simp
      split_ifs <;> simp