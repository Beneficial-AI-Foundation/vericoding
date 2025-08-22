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
def checkPrime (n: Nat) : Bool :=
if n < 2 then false
else if n = 2 then true
else if n % 2 = 0 then false
else
let rec aux (d: Nat) : Bool :=
if d * d > n then true
else if n % d = 0 then false
else aux (d + 2)
termination_by n - d * d
decreasing_by
  simp_wf
  have h1 : d * d ≤ n := by
    by_contra h_contra
    simp at h_contra
    exact h_contra h‿¹
  have h2 : n - (d + 2) * (d + 2) < n - d * d := by
    have : (d + 2) * (d + 2) = d * d + 4 * d + 4 := by ring
    rw [this]
    have : d * d + 4 * d + 4 > d * d := by omega
    have : d * d < n := by
      by_contra h_not_lt
      simp at h_not_lt
      exact h‿¹ h_not_lt
    omega
  exact h2
aux 3

-- LLM HELPER
lemma checkPrime_correct (n: Nat) : checkPrime n = true ↔ Nat.Prime n := by
  constructor
  · intro h
    unfold checkPrime at h
    split at h
    · simp at h
    · split at h
      · simp at h
        rw [h]
        exact Nat.prime_two
      · split at h
        · simp at h
        · simp at h
          have : n ≥ 2 := by omega
          have : Odd n := by
            rw [Nat.odd_iff_not_even, Nat.even_iff_two_dvd]
            intro ⟨k, hk⟩
            have : n % 2 = 0 := Nat.mod_eq_zero_of_dvd ⟨k, hk⟩
            simp at this
          apply Nat.Prime.of_odd_min_fac this
          induction n using Nat.strong_induction_on with
          | ind n ih => 
            rw [Nat.minFac_eq_two_or_odd]
            cases' h_min : Nat.minFac n with
            | zero => simp at h_min
            | succ m => simp
  · intro h
    unfold checkPrime
    split
    · have : n ≥ 2 := Nat.Prime.two_le h
      omega
    · split
      · simp
      · split
        · have : n ≠ 2 := by omega
          have : Even n := Nat.even_iff_two_dvd.mpr ⟨n / 2, by assumption⟩
          have : ¬Nat.Prime n := Nat.Prime.not_even h this
          contradiction
        · simp
          induction n using Nat.strong_induction_on with
          | ind n ih => 
            have : n ≥ 2 := Nat.Prime.two_le h
            exact True.intro

def implementation (interval1: Int × Int) (interval2: Int × Int) : String :=
let (s1, e1) := interval1
let (s2, e2) := interval2
if s1 > e1 ∨ s2 > e2 then "NO"
else
  let intersectionStart := max s1 s2
  let intersectionEnd := min e1 e2
  if intersectionStart > intersectionEnd then "NO"
  else
    let length := (intersectionEnd - intersectionStart).toNat
    if checkPrime length then "YES" else "NO"

theorem correctness
(interval1: Int × Int)
(interval2: Int × Int)
: problem_spec implementation interval1 interval2 := by
  simp [problem_spec]
  use implementation interval1 interval2
  constructor
  · rfl
  · intro h1 h2
    let (s1, e1) := interval1
    let (s2, e2) := interval2
    simp [implementation]
    have valid1 : ¬(s1 > e1) := by omega
    have valid2 : ¬(s2 > e2) := by omega
    simp [valid1, valid2]
    let intersectionStart := max s1 s2
    let intersectionEnd := min e1 e2
    by_cases h_intersect : intersectionStart ≤ intersectionEnd
    · simp [h_intersect]
      let length := (intersectionEnd - intersectionStart).toNat
      by_cases h_prime : checkPrime length
      · simp [h_prime]
        constructor
        · constructor
          · intro
            constructor
            · exact h_intersect
            · rw [← checkPrime_correct]
              exact h_prime
          · intro ⟨_, h_prime_nat⟩
            rfl
        · constructor
          · intro h_contra
            simp at h_contra
          · intro h_contra
            cases h_contra with
            | inl h_no_intersect => exact absurd h_intersect h_no_intersect
            | inr h_not_prime => 
              rw [checkPrime_correct] at h_prime
              exact absurd h_prime h_not_prime
      · simp [h_prime]
        constructor
        · constructor
          · intro h_contra
            simp at h_contra
          · intro h_contra
            cases h_contra with
            | inl h_no_intersect => exact absurd h_intersect h_no_intersect
            | inr h_not_prime => rfl
        · constructor
          · intro
            right
            rw [← checkPrime_correct]
            exact h_prime
          · intro
            rfl
    · simp [h_intersect]
      constructor
      · constructor
        · intro h_contra
          simp at h_contra
        · intro h_contra
          cases h_contra with
          | inl h_no_intersect => rfl
          | inr h_not_prime => rfl
      · constructor
        · intro
          left
          exact h_intersect
        · intro
          rfl