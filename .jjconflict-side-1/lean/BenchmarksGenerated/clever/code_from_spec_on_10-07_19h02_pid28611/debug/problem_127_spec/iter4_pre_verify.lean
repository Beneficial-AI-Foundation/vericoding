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
if (interval1.1 ≤ interval1.2 ∧ interval2.1 ≤ interval1.2) ∧ 
   (interval1.1 ≤ interval2.2 ∧ interval2.1 ≤ interval2.2) then
  if Nat.Prime (interval1.2 ⊓ interval2.2 - interval1.1 ⊔ interval2.1).toNat then "YES" else "NO"
else "NO"

theorem correctness
(interval1: Int × Int)
(interval2: Int × Int)
: problem_spec implementation interval1 interval2 := by
  let (s1, e1) := interval1
  let (s2, e2) := interval2
  use implementation interval1 interval2
  constructor
  · simp [s1, e1, s2, e2]
  · intro h1 h2
    let intersectionStart := max s1 s2
    let intersectionEnd := min e1 e2
    let hasIntersection := intersectionStart ≤ intersectionEnd
    let isPrime := Nat.Prime (intersectionEnd - intersectionStart).toNat
    
    simp [implementation]
    simp [s1, e1, s2, e2]
    simp [intersectionStart, intersectionEnd, hasIntersection, isPrime]
    simp [max_def, min_def]
    
    constructor
    · constructor
      · intro h
        split_ifs at h with h_valid h_prime
        · simp at h
          constructor
          · simp at h_valid
            exact h_valid.2.1
          · exact h_prime
        · simp at h
        · simp at h
      · intro ⟨hInt, hPrime⟩
        simp [hInt, hPrime]
        constructor
        · constructor
          · exact h1
          · exact h2
        · constructor
          · exact h1
          · exact h2
    
    constructor
    · constructor
      · intro h
        split_ifs at h with h_valid h_prime
        · simp at h
          right
          exact h_prime
        · left
          simp at h_valid
          push_neg at h_valid
          cases' h_valid with h_case h_case
          · cases' h_case with h_ne h_ne
            · exact le_refl _
            · exact le_refl _
          · cases' h_case with h_ne h_ne
            · exact le_refl _
            · exact le_refl _
        · left
          simp at h_valid
          push_neg at h_valid
          cases' h_valid with h_case h_case
          · cases' h_case with h_ne h_ne
            · exact le_refl _
            · exact le_refl _
          · cases' h_case with h_ne h_ne
            · exact le_refl _
            · exact le_refl _
      · intro h
        cases' h with h h
        · simp [h]
          split_ifs
          · simp
          · rfl
          · rfl
        · simp
          split_ifs with h_valid h_prime
          · simp [h_prime]
          · rfl
          · rfl
    
    · split_ifs
      · split_ifs
        · left; rfl
        · right; rfl
      · right; rfl