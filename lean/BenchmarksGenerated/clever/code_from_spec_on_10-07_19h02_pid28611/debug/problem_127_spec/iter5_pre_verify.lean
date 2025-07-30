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
        split_ifs at h with h_int h_prime
        · simp at h
          constructor
          · exact h_int
          · exact h_prime.2
        · simp at h
        · simp at h
      · intro ⟨hInt, hPrime⟩
        simp [hInt, hPrime]
        constructor
        · exact le_trans (le_refl _) (Int.sub_nonneg_of_le hInt)
        · exact hPrime
    
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
        · simp [h]
          split_ifs
          · simp
          · rfl
          · rfl
        · simp
          split_ifs with h_int h_prime
          · simp [h_prime]
          · rfl
          · rfl
    
    · split_ifs
      · split_ifs
        · left; rfl
        · right; rfl
      · right; rfl