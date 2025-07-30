-- LLM HELPER
def Even (n: Int) : Prop := ∃ k, n = 2 * k

-- LLM HELPER
def Odd (n: Int) : Prop := ∃ k, n = 2 * k + 1

def problem_spec
(implementation: Int → Int → Int)
(x: Int) (y: Int) :=
let spec (result: Int) :=
  (result = -1 ∨ (x ≤ result ∧ result ≤ y ∧ Even result)) ∧
  (result = -1 ∨ (∀ i: Int, (x ≤ i ∧ i ≤ y ∧ Even i) → result ≥ i)) ∧
  (result = -1 ↔ (x > y ∨ (x = y ∧ Odd x ∧ Odd y)))
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
lemma even_iff_mod_two_eq_zero (n: Int) : Even n ↔ n % 2 = 0 := by
  constructor
  · intro ⟨k, hk⟩
    rw [hk]
    exact Int.mul_emod_right 2 k
  · intro h
    use n / 2
    exact Int.div_add_mod n 2 ▸ by simp [h]

-- LLM HELPER
lemma odd_iff_mod_two_eq_one (n: Int) : Odd n ↔ n % 2 = 1 := by
  constructor
  · intro ⟨k, hk⟩
    rw [hk]
    simp [Int.add_mul_emod_self_left]
  · intro h
    use (n - 1) / 2
    have : n = 2 * ((n - 1) / 2) + 1 := by
      rw [← Int.div_add_mod (n - 1) 2]
      congr 1
      have : (n - 1) % 2 = 0 := by
        have : n % 2 = 1 := h
        rw [← Int.sub_emod]
        simp [this]
      rw [this, add_zero]
      ring
    exact this

-- LLM HELPER
lemma nextEven_spec (n: Int) : Even (nextEven n) ∧ nextEven n ≥ n := by
  unfold nextEven
  by_cases h : n % 2 = 0
  · simp [h]
    constructor
    · rw [even_iff_mod_two_eq_zero]
      exact h
    · rfl
  · simp [h]
    constructor
    · rw [even_iff_mod_two_eq_zero]
      simp [Int.add_emod]
      have : n % 2 = 1 := by
        have : n % 2 = 0 ∨ n % 2 = 1 := Int.mod_two_eq_zero_or_one n
        cases this with
        | inl h0 => exact absurd h0 h
        | inr h1 => exact h1
      rw [this]
      norm_num
    · linarith

-- LLM HELPER
lemma nextEven_minimal (n: Int) (m: Int) : Even m → m ≥ n → m ≥ nextEven n := by
  intros h_even h_ge
  unfold nextEven
  by_cases h : n % 2 = 0
  · simp [h]
    exact h_ge
  · simp [h]
    have h_odd : Odd n := by
      rw [odd_iff_mod_two_eq_one]
      have : n % 2 = 0 ∨ n % 2 = 1 := Int.mod_two_eq_zero_or_one n
      cases this with
      | inl h0 => exact absurd h0 h
      | inr h1 => exact h1
    by_contra h_not
    push_neg at h_not
    have h_lt : m < n + 1 := h_not
    have h_le : m ≤ n := by linarith
    have h_eq : m = n := le_antisymm h_le h_ge
    rw [h_eq] at h_even
    rw [even_iff_mod_two_eq_zero] at h_even
    rw [odd_iff_mod_two_eq_one] at h_odd
    rw [h_even] at h_odd
    norm_num at h_odd

theorem correctness
(x: Int) (y: Int) : problem_spec implementation x y := by
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
        · simp
          left
          exact h1
    · simp [h1]
      by_cases h2 : x = y ∧ x % 2 = 1
      · simp [h2]
        constructor
        · left; rfl
        · constructor
          · left; rfl
          · simp
            right
            constructor
            · exact h2.1
            · constructor
              · rw [odd_iff_mod_two_eq_one]
                exact h2.2
              · rw [← h2.1]
                rw [odd_iff_mod_two_eq_one]
                exact h2.2
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
            · simp
              intro h_or
              cases h_or with
              | inl h_gt => exact absurd h_gt h1
              | inr h_and => 
                have h_not_both : ¬(x = y ∧ x % 2 = 1) := h2
                have h_mod : x % 2 = 1 := by
                  rw [← odd_iff_mod_two_eq_one]
                  exact h_and.2.1
                have h_and_mod : x = y ∧ x % 2 = 1 := ⟨h_and.1, h_mod⟩
                exact absurd h_and_mod h_not_both
        · simp [h3]
          constructor
          · left; rfl
          · constructor
            · left; rfl
            · simp
              right
              have h_ge_x : start ≥ x := (nextEven_spec x).2
              have h_le_y : x ≤ y := le_of_not_gt h1
              have h_even : Even start := (nextEven_spec x).1
              constructor
              · by_contra h_not_gt
                push_neg at h_not_gt
                have h_le_y' : start ≤ y := h_not_gt
                exact absurd h_le_y' h3
              · constructor
                · rw [odd_iff_mod_two_eq_one]
                  by_contra h_not_odd
                  have h_eq : start = y := by
                    by_contra h_ne
                    have h_lt : start < y := by
                      have h_le : start ≤ y := by
                        by_contra h_not_le
                        exact h3 h_not_le
                      exact lt_of_le_of_ne h_le h_ne
                    exact h3 h_lt
                  rw [h_eq] at h_even
                  rw [even_iff_mod_two_eq_zero] at h_even
                  have : y % 2 = 1 := by
                    rw [← h_le_y.antisymm (le_of_not_gt h1)]
                    have : ¬(x = y ∧ x % 2 = 1) := h2
                    simp at this
                    rw [le_antisymm h_le_y (le_of_not_gt h1)] at this
                    exact this (le_antisymm h_le_y (le_of_not_gt h1))
                  rw [this] at h_even
                  norm_num at h_even
                · rw [le_antisymm h_le_y (le_of_not_gt h1)]
                  rw [odd_iff_mod_two_eq_one]
                  by_contra h_not_odd_y
                  have h_eq : start = y := by
                    by_contra h_ne
                    have h_lt : start < y := by
                      have h_le : start ≤ y := by
                        by_contra h_not_le
                        exact h3 h_not_le
                      exact lt_of_le_of_ne h_le h_ne
                    exact h3 h_lt
                  rw [h_eq] at h_even
                  rw [even_iff_mod_two_eq_zero] at h_even
                  have : y % 2 = 1 := by
                    have h_xy : x = y := le_antisymm h_le_y (le_of_not_gt h1)
                    have h_not_both : ¬(x = y ∧ x % 2 = 1) := h2
                    simp at h_not_both
                    rw [h_xy] at h_not_both
                    exact h_not_both h_xy
                  rw [this] at h_even
                  norm_num at h_even