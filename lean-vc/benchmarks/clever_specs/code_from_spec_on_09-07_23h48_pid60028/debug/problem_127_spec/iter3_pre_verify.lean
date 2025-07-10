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
  have h1 : d * d ≤ n := by linarith
  have h2 : (d + 2) * (d + 2) = d * d + 4 * d + 4 := by ring
  rw [h2]
  linarith
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

-- LLM HELPER
lemma toNat_sub_nonneg (a b : Int) (h : a ≥ b) : (a - b).toNat = (a - b).natAbs := by
  rw [Int.toNat_eq_natAbs_of_nonneg]
  linarith

-- LLM HELPER
lemma max_le_iff {a b c : Int} : max a b ≤ c ↔ a ≤ c ∧ b ≤ c := by
  constructor
  · intro h
    exact ⟨le_trans (le_max_left a b) h, le_trans (le_max_right a b) h⟩
  · intro ⟨h1, h2⟩
    exact max_le h1 h2

-- LLM HELPER
lemma min_le_max {a b c d : Int} (h1 : a ≤ b) (h2 : c ≤ d) : min b d ≥ max a c ↔ a ≤ d ∧ c ≤ b := by
  constructor
  · intro h
    constructor
    · have : a ≤ max a c := le_max_left a c
      have : max a c ≤ min b d := h
      have : min b d ≤ d := min_le_right b d
      linarith
    · have : c ≤ max a c := le_max_right a c
      have : max a c ≤ min b d := h
      have : min b d ≤ b := min_le_left b d
      linarith
  · intro ⟨h3, h4⟩
    have : max a c ≤ b := by
      rw [max_le_iff]
      exact ⟨le_trans h1 h3, h4⟩
    have : max a c ≤ d := by
      rw [max_le_iff]
      exact ⟨h3, le_trans h2 h4⟩
    exact le_min this (le_trans (le_max_left a c) (le_trans h1 h3))

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
                rw [h_contra] at h_prime
                simp at h_prime
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
                rw [h_contra] at h_prime
                simp at h_prime
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
              rw [h_contra] at h_intersect
              simp at h_intersect
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
            rw [h_contra] at h_valid2
            simp at h_valid2
          · intro h_contra
            cases h_contra with
            | inl h_no_intersect => rfl
            | inr h_not_prime => rfl
        · constructor
          · intro
            left
            let intersectionStart := max s1 s2
            let intersectionEnd := min e1 e2
            by_contra h_has_intersect
            have : s2 ≤ e2 := by
              have : intersectionStart ≤ intersectionEnd := h_has_intersect
              rw [min_le_max h1 h2] at this
              exact this.2
            exact h_valid2 this
          · intro
            rfl
    · simp [h_valid1]
      constructor
      · constructor
        · intro h_contra
          rw [h_contra] at h_valid1
          simp at h_valid1
        · intro h_contra
          cases h_contra with
          | inl h_no_intersect => rfl
          | inr h_not_prime => rfl
      · constructor
        · intro
          left
          let intersectionStart := max s1 s2
          let intersectionEnd := min e1 e2
          by_contra h_has_intersect
          have : s1 ≤ e1 := by
            have : intersectionStart ≤ intersectionEnd := h_has_intersect
            rw [min_le_max h1 h2] at this
            exact this.1
          exact h_valid1 this
        · intro
          rfl