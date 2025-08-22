def problem_spec
(implementation: Int → Int → Int)
(x: Int) (y: Int) :=
let spec (result: Int) :=
  (result = -1 ∨ (x ≤ result ∧ result ≤ y ∧ Even result)) ∧
  (result = -1 ∨ (∀ i: Int, (x ≤ i ∧ i ≤ y ∧ Even i) → result ≥ i)) ∧
  (result = -1 ↔ (x > y ∨ (x == y ∧ Odd x ∧ Odd y)))
∃ result, implementation x y = result ∧
spec result

-- LLM HELPER
def nextEven (n: Int) : Int :=
  if n % 2 = 0 then n else n + 1

def implementation (x: Int) (y: Int) : Int := 
  if x > y then -1
  else if x = y ∧ x % 2 = 1 then -1
  else
    let start := nextEven x
    if start ≤ y then start else -1

-- LLM HELPER
lemma nextEven_spec (n: Int) : Even (nextEven n) ∧ nextEven n ≥ n := by
  unfold nextEven
  by_cases h : n % 2 = 0
  · simp [h]
    constructor
    · exact Int.dvd_iff_emod_eq_zero.mpr h
    · rfl
  · simp [h]
    constructor
    · rw [Int.even_add_one]
      exact Int.odd_iff_not_even.mp (Int.odd_iff_not_even.mpr (mt Int.dvd_iff_emod_eq_zero.mp h))
    · linarith

-- LLM HELPER
lemma nextEven_minimal (n: Int) (m: Int) : Even m → m ≥ n → m ≥ nextEven n := by
  intros h_even h_ge
  unfold nextEven
  by_cases h : n % 2 = 0
  · simp [h]
    exact h_ge
  · simp [h]
    have h_odd : Odd n := Int.odd_iff_not_even.mpr (mt Int.dvd_iff_emod_eq_zero.mp h)
    have h_even_ge : m ≥ n + 1 := by
      by_contra h_not
      push_neg at h_not
      have h_lt : m < n + 1 := h_not
      have h_le : m ≤ n := by linarith
      have h_ge_n : m ≥ n := h_ge
      have h_eq : m = n := le_antisymm h_le h_ge_n
      rw [h_eq] at h_even
      exact Int.odd_iff_not_even.mp h_odd h_even
    exact h_even_ge

theorem correctness
(x: Int) (y: Int)
: problem_spec implementation x y := by
  unfold problem_spec
  use implementation x y
  constructor
  · rfl
  · unfold implementation
    by_cases h1 : x > y
    · simp [h1]
      constructor
      · left; rfl
      · constructor
        · left; rfl
        · constructor
          · left; rfl
          · left; exact h1
    · simp [h1]
      by_cases h2 : x = y ∧ x % 2 = 1
      · simp [h2]
        constructor
        · left; rfl
        · constructor
          · left; rfl
          · constructor
            · right
              constructor
              · exact h2.1
              · constructor
                · exact Int.odd_iff_not_even.mpr (mt Int.dvd_iff_emod_eq_zero.mp h2.2)
                · rw [← h2.1]
                  exact Int.odd_iff_not_even.mpr (mt Int.dvd_iff_emod_eq_zero.mp h2.2)
            · simp
              right
              exact ⟨h2.1, Int.odd_iff_not_even.mpr (mt Int.dvd_iff_emod_eq_zero.mp h2.2), 
                     rw [← h2.1]; exact Int.odd_iff_not_even.mpr (mt Int.dvd_iff_emod_zero.mp h2.2)⟩
      · simp [h2]
        let start := nextEven x
        by_cases h3 : start ≤ y
        · simp [h3]
          have h_even : Even start := (nextEven_spec x).1
          have h_ge_x : start ≥ x := (nextEven_spec x).2
          constructor
          · right
            exact ⟨le_trans h_ge_x (le_of_not_gt h1), h3, h_even⟩
          · constructor
            · right
              intros i h_cond
              exact nextEven_minimal x i h_cond.2.2 h_cond.1
            · constructor
              · intro h_false
                simp at h_false
              · intro h_or
                cases h_or with
                | inl h_gt => exact absurd h_gt h1
                | inr h_and => 
                  have h_not_both : ¬(x = y ∧ x % 2 = 1) := h2
                  exact absurd h_and h_not_both
        · simp [h3]
          constructor
          · left; rfl
          · constructor
            · left; rfl
            · constructor
              · left; rfl
              · simp
                have h_ge_x : start ≥ x := (nextEven_spec x).2
                have h_le_y : x ≤ y := le_of_not_gt h1
                left
                by_contra h_not_gt
                push_neg at h_not_gt
                have h_le_y' : start ≤ y := h_not_gt
                exact absurd h_le_y' h3