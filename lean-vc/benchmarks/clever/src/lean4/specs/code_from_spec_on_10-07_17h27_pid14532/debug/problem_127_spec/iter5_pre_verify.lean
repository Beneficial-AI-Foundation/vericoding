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
    let lengthNat := length.toNat
    if Nat.Prime lengthNat then "YES" else "NO"
  else "NO"
else "NO"

theorem correctness
(interval1: Int × Int)
(interval2: Int × Int)
: problem_spec implementation interval1 interval2 := by
  unfold problem_spec
  use implementation interval1 interval2
  constructor
  · rfl
  · unfold implementation
    intro h1 h2
    let s1 := interval1.1
    let e1 := interval1.2
    let s2 := interval2.1
    let e2 := interval2.2
    let intersectionStart := s1 ⊔ s2
    let intersectionEnd := e1 ⊓ e2
    let hasIntersection := intersectionStart ≤ intersectionEnd
    let isPrime := Nat.Prime (intersectionEnd - intersectionStart).toNat
    constructor
    · constructor
      · intro h
        simp only [max_def, min_def] at h ⊢
        split_ifs at h with h_int h_nonneg h_prime
        · constructor
          · exact h_int
          · exact h_prime
        · exfalso
          simp at h
        · exfalso
          have h_le : intersectionStart ≤ intersectionEnd := h_int
          have : intersectionEnd - intersectionStart ≥ 0 := by linarith
          exact h_nonneg this
        · exfalso
          simp at h
      · intro ⟨h_int, h_prime⟩
        simp only [max_def, min_def]
        split_ifs with h_int' h_nonneg h_prime'
        · rfl
        · exfalso
          exact h_int' h_int
        · exfalso
          have : intersectionEnd - intersectionStart ≥ 0 := by linarith
          exact h_nonneg this
        · contradiction
    constructor
    · constructor
      · intro h
        simp only [max_def, min_def] at h ⊢
        split_ifs at h with h_int h_nonneg h_prime
        · exfalso
          simp at h
        · left
          exact h_int
        · right
          intro h_prime_pos
          have h_le : intersectionStart ≤ intersectionEnd := h_int
          have : intersectionEnd - intersectionStart ≥ 0 := by linarith
          exact h_nonneg this
        · right
          exact h_prime
      · intro h
        simp only [max_def, min_def]
        cases' h with h_no_int h_not_prime
        · split_ifs with h_int h_nonneg h_prime
          · exfalso
            exact h_no_int h_int
          · rfl
          · rfl
          · rfl
        · split_ifs with h_int h_nonneg h_prime
          · exfalso
            exact h_not_prime h_prime
          · rfl
          · rfl
          · rfl
    · simp only [max_def, min_def]
      split_ifs
      · left; rfl
      · right; rfl
      · right; rfl
      · right; rfl