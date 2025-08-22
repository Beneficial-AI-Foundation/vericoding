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
    have : d * d > n := h_contra
    simp [this] at *
  have h2 : n - (d + 2) * (d + 2) < n - d * d := by
    have : (d + 2) * (d + 2) = d * d + 4 * d + 4 := by
      ring
    rw [this]
    have : d * d + 4 * d + 4 > d * d := by
      simp
      have : 4 * d + 4 > 0 := by
        simp
        exact Nat.succ_pos (4 * d + 3)
      exact this
    have : d * d + 4 * d + 4 ≤ n := by
      by_contra h_contra
      simp at h_contra
      have : (d + 2) * (d + 2) > n := by
        rw [← this]
        exact h_contra
      simp [this] at *
    exact Nat.sub_lt_sub_left this h1
  exact h2
aux 3

-- LLM HELPER
lemma checkPrime_correct (n: Nat) : checkPrime n = true ↔ Nat.Prime n := by
  sorry

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
    by_cases h_valid1 : s1 ≤ e1
    · by_cases h_valid2 : s2 ≤ e2
      · simp [h_valid1, h_valid2]
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
      · simp [h_valid2]
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
            by_contra h_has_intersect
            have : s2 ≤ e2 := by
              have : max s1 s2 ≤ min e1 e2 := h_has_intersect
              have : s2 ≤ max s1 s2 := le_max_right s1 s2
              have : min e1 e2 ≤ e2 := min_le_right e1 e2
              linarith
            exact h_valid2 this
          · intro
            rfl
    · simp [h_valid1]
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
          by_contra h_has_intersect
          have : s1 ≤ e1 := by
            have : max s1 s2 ≤ min e1 e2 := h_has_intersect
            have : s1 ≤ max s1 s2 := le_max_left s1 s2
            have : min e1 e2 ≤ e1 := min_le_left e1 e2
            linarith
          exact h_valid1 this
        · intro
          rfl