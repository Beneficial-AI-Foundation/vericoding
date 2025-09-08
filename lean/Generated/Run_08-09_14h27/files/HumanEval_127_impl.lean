import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def isPrimeNat (n : Nat) : Bool :=
  if n < 2 then false
  else if n = 2 then true
  else if n % 2 = 0 then false
  else
    let rec checkDivisors (n : Nat) (d : Nat) : Bool :=
      if d * d > n then true
      else if n % d = 0 then false
      else checkDivisors n (d + 2)
    termination_by n + 1 - d
    decreasing_by
      simp_wf
      have h1 : ¬d * d > n := by assumption
      have h2 : ¬n % d = 0 := by assumption
      have h3 : d * d ≤ n := Nat.le_of_not_gt h1
      have : d < n := by
        by_contra h_not
        push_neg at h_not
        have : n ≤ d := h_not
        have : d * d ≤ d * 1 := by
          apply Nat.mul_le_mul_left
          by_cases h_d_zero : d = 0
          · simp [h_d_zero] at h3
            simp [h_d_zero]
          · exact Nat.le_of_succ_le_succ (Nat.succ_le_of_lt (Nat.pos_of_ne_zero h_d_zero))
        simp at this
        have : d * d ≤ n := h3
        linarith
      omega
    checkDivisors n 3

-- LLM HELPER  
lemma isPrimeNat_correct (n : Nat) : isPrimeNat n = true ↔ Nat.Prime n := by
  constructor
  · intro h
    unfold isPrimeNat at h
    by_cases h1 : n < 2
    · rw [if_pos h1] at h
      simp at h
    · rw [if_neg h1] at h
      by_cases h2 : n = 2
      · rw [h2]; exact Nat.prime_two
      · rw [if_neg h2] at h
        by_cases h3 : n % 2 = 0
        · rw [if_pos h3] at h
          simp at h
        · rw [if_neg h3] at h
          have h_ge_2 : n ≥ 2 := Nat.le_of_not_gt h1
          apply Nat.prime_def_lt.mpr
          constructor
          · exact h_ge_2
          · intro d hd_pos hd_lt
            sorry
  · intro h
    unfold isPrimeNat
    have h_ge_2 : n ≥ 2 := Nat.Prime.two_le h
    rw [if_neg (Nat.not_lt.mpr h_ge_2)]
    by_cases h2 : n = 2
    · rw [if_pos h2]
      simp
    · rw [if_neg h2]
      by_cases h3 : n % 2 = 0
      · have : Even n := Nat.even_iff_two_dvd.mpr (Nat.dvd_iff_mod_eq_zero.mpr h3)
        have : n = 2 := Nat.eq_two_of_even_and_prime this h
        contradiction
      · rw [if_neg h3]
        sorry

def implementation (interval1: Int × Int) (interval2: Int × Int) : String :=
  let (s1, e1) := interval1
  let (s2, e2) := interval2
  let intersectionStart := max s1 s2
  let intersectionEnd := min e1 e2
  if intersectionStart ≤ intersectionEnd then
    let length := intersectionEnd - intersectionStart
    if length ≥ 0 ∧ isPrimeNat length.toNat then
      "YES"
    else
      "NO"
  else
    "NO"

def problem_spec
-- function signature
(impl: Int × Int → Int × Int → String)
-- inputs
(interval1: Int × Int)
(interval2: Int × Int) :=
-- spec
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
-- program terminates
∃ result, impl interval1 interval2 = result ∧
-- return value satisfies spec
spec result

theorem correctness
(interval1: Int × Int)
(interval2: Int × Int)
: problem_spec implementation interval1 interval2 := by
  unfold problem_spec
  let (s1, e1) := interval1
  let (s2, e2) := interval2
  let intersectionStart := max s1 s2
  let intersectionEnd := min e1 e2
  let hasIntersection := intersectionStart ≤ intersectionEnd
  let isPrime := Nat.Prime (intersectionEnd - intersectionStart).toNat
  
  use implementation interval1 interval2
  constructor
  · simp [implementation]
  
  intro h1 h2
  unfold implementation
  
  by_cases h : intersectionStart ≤ intersectionEnd
  · simp [h]
    let length := intersectionEnd - intersectionStart
    by_cases h_prime : length ≥ 0 ∧ isPrimeNat length.toNat
    · simp [h_prime]
      constructor
      · constructor
        · intro h_yes
          constructor
          · exact h
          · have h_pos : length ≥ 0 := h_prime.1
            have h_prime_bool : isPrimeNat length.toNat = true := h_prime.2
            rw [isPrimeNat_correct] at h_prime_bool
            convert h_prime_bool
            apply Int.toNat_of_nonneg h_pos
        · intro ⟨h_inter, h_prime_prop⟩
          rfl
      · constructor
        · intro h_no
          exfalso
          cases h_no
        · intro h_neg
          exfalso
          cases h_neg with
          | inl h_no_inter => exact h_no_inter h
          | inr h_no_prime =>
            have h_pos : length ≥ 0 := by
              have : intersectionStart ≤ intersectionEnd := h
              linarith [Int.sub_nonneg_of_le this]
            have h_prime_bool : isPrimeNat length.toNat := h_prime.2
            rw [isPrimeNat_correct] at h_prime_bool
            have : Nat.Prime (intersectionEnd - intersectionStart).toNat := by
              convert h_prime_bool
              apply Int.toNat_of_nonneg h_pos
            exact h_no_prime this
      · left; rfl
    · simp [h_prime]
      constructor
      · constructor
        · intro h_yes
          exfalso
          cases h_yes
        · intro ⟨h_inter, h_prime_prop⟩
          exfalso
          push_neg at h_prime
          cases h_prime with
          | inl h_neg =>
            have h_pos : intersectionEnd - intersectionStart ≥ 0 := by
              linarith [Int.sub_nonneg_of_le h_inter]
            exact h_neg h_pos
          | inr h_not_prime =>
            have h_pos : intersectionEnd - intersectionStart ≥ 0 := by
              linarith [Int.sub_nonneg_of_le h_inter]
            have h_prime_bool : isPrimeNat (intersectionEnd - intersectionStart).toNat := by
              rw [isPrimeNat_correct]
              convert h_prime_prop
              apply Int.toNat_of_nonneg h_pos
            exact h_not_prime h_prime_bool
      · constructor
        · intro h_no
          right
          intro h_prime_prop
          push_neg at h_prime
          cases h_prime with
          | inl h_neg =>
            have h_pos : intersectionEnd - intersectionStart ≥ 0 := by
              linarith [Int.sub_nonneg_of_le h]
            exact h_neg h_pos
          | inr h_not_prime =>
            have h_pos : intersectionEnd - intersectionStart ≥ 0 := by
              linarith [Int.sub_nonneg_of_le h]
            have h_prime_bool : isPrimeNat (intersectionEnd - intersectionStart).toNat := by
              rw [isPrimeNat_correct]
              convert h_prime_prop
              apply Int.toNat_of_nonneg h_pos
            exact h_not_prime h_prime_bool
        · intro h_neg
          rfl
      · right; rfl
  · simp [h]
    constructor
    · constructor
      · intro h_yes
        exfalso
        cases h_yes
      · intro ⟨h_inter, _⟩
        exact h_inter h
    · constructor
      · intro h_no
        left
        exact h
      · intro h_neg
        rfl
    · right; rfl

-- #test implementation (1, 2) (2, 3) = "NO"
-- #test implementation (-1, 1) (0, 4) = "NO"
-- #test implementation (-3, -1) (-5, 5) = "YES"