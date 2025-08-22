def problem_spec
-- function signature
(implementation: Int → Bool)
-- inputs
(a: Int) :=
-- spec
let spec (result: Bool) :=
  result ↔ exists n: Int, a = n^3
-- program termination
∃ result, implementation a = result ∧
spec result

-- LLM HELPER
def cube_root_int (a: Int) : Int :=
  if a ≥ 0 then
    Int.natAbs (Int.floor (a.natAbs : Real) ^ (1/3 : Real))
  else
    -Int.natAbs (Int.floor ((-a).natAbs : Real) ^ (1/3 : Real))

-- LLM HELPER
def is_perfect_cube (a: Int) : Bool :=
  let cr := cube_root_int a
  (cr^3 = a) || ((cr+1)^3 = a) || ((cr-1)^3 = a)

def implementation (a: Int) : Bool := is_perfect_cube a

-- LLM HELPER
lemma cube_root_bounds (a: Int) (h: a ≥ 0) : 
  let cr := cube_root_int a
  cr^3 ≤ a ∧ a < (cr+1)^3 := by
  constructor
  · simp [cube_root_int]
    split_ifs with h1
    · simp
      have : (Int.natAbs (Int.floor (a.natAbs : Real) ^ (1/3 : Real)))^3 ≤ a := by
        have h_pos : (0 : Real) ≤ a.natAbs := by simp
        have h_cube : (Int.floor (a.natAbs : Real) ^ (1/3 : Real))^3 ≤ a.natAbs := by
          rw [Int.floor_le]
          exact Real.rpow_natCast_mul _ _ (by norm_num)
        exact Int.coe_nat_le_coe_nat_iff.mp h_cube
      exact this
    · exfalso; exact h1 h
  · simp [cube_root_int]
    split_ifs with h1
    · simp
      have : a < (Int.natAbs (Int.floor (a.natAbs : Real) ^ (1/3 : Real)) + 1)^3 := by
        have h_pos : (0 : Real) ≤ a.natAbs := by simp
        have h_cube : a.natAbs < (Int.floor (a.natAbs : Real) ^ (1/3 : Real) + 1)^3 := by
          rw [Int.lt_floor_add_one]
          exact Real.rpow_natCast_mul _ _ (by norm_num)
        exact Int.coe_nat_lt_coe_nat_iff.mp h_cube
      exact this
    · exfalso; exact h1 h

-- LLM HELPER
lemma perfect_cube_correct (a: Int) : 
  is_perfect_cube a = true ↔ ∃ n: Int, a = n^3 := by
  constructor
  · intro h
    unfold is_perfect_cube at h
    simp at h
    let cr := cube_root_int a
    cases' h with h1 h2
    · use cr; exact h1
    · cases' h2 with h2 h3
      · use cr + 1; exact h2
      · use cr - 1; exact h3
  · intro ⟨n, hn⟩
    unfold is_perfect_cube
    simp
    let cr := cube_root_int a
    by_cases h1: cr^3 = a
    · left; exact h1
    · by_cases h2: (cr+1)^3 = a
      · right; left; exact h2
      · right; right
        rw [←hn]
        have : n = cr - 1 := by
          have h_near : (cr - 1)^3 ≤ a ∧ a ≤ (cr + 1)^3 := by
            constructor
            · by_cases h_pos : a ≥ 0
              · have h_bounds := cube_root_bounds a h_pos
                have : cr^3 ≤ a := h_bounds.1
                have : (cr - 1)^3 < cr^3 := by
                  ring_nf
                  simp
                omega
              · simp [cube_root_int] at cr
                split_ifs at cr with h_split
                · contradiction
                · simp at cr
                  have : a < 0 := by omega
                  have : (cr - 1)^3 < 0 := by
                    have : cr < 0 := by simp [cr]
                    have : cr - 1 < cr := by omega
                    have : cr - 1 < 0 := by omega
                    exact Int.pow_neg_of_odd this (by norm_num)
                  omega
            · by_cases h_pos : a ≥ 0
              · have h_bounds := cube_root_bounds a h_pos
                have : a < (cr + 1)^3 := h_bounds.2
                omega
              · simp [cube_root_int] at cr
                split_ifs at cr with h_split
                · contradiction
                · simp at cr
                  have : a < 0 := by omega
                  have : (cr + 1)^3 > a := by
                    have : cr < 0 := by simp [cr]
                    by_cases h_cr : cr + 1 ≤ 0
                    · have : (cr + 1)^3 ≤ 0 := by
                        cases' Int.le_iff_lt_or_eq.mp h_cr with h_lt h_eq
                        · exact Int.pow_neg_of_odd h_lt (by norm_num)
                        · simp [h_eq]
                      omega
                    · have : (cr + 1)^3 > 0 := by
                        have : cr + 1 > 0 := by omega
                        exact Int.pow_pos this
                      omega
                  omega
          rw [hn] at h_near
          have h_unique : ∀ m : Int, m^3 = n^3 → m = n := by
            intros m hm
            exact Int.eq_of_pow_eq_pow_of_odd hm (by norm_num)
          by_cases h_eq1 : (cr - 1)^3 = n^3
          · exact h_unique (cr - 1) h_eq1
          · by_cases h_eq2 : cr^3 = n^3
            · have : cr = n := h_unique cr h_eq2
              rw [this] at h1
              contradiction
            · by_cases h_eq3 : (cr + 1)^3 = n^3
              · have : cr + 1 = n := h_unique (cr + 1) h_eq3
                rw [this] at h2
                contradiction
              · have : n^3 = a := hn
                have : (cr - 1)^3 ≤ a ∧ a ≤ (cr + 1)^3 := h_near
                have : (cr - 1)^3 ≤ n^3 ∧ n^3 ≤ (cr + 1)^3 := by rw [←this]; exact h_near
                omega
        rw [this, hn]

theorem correctness
(a: Int)
: problem_spec implementation a := by
  unfold problem_spec implementation
  use is_perfect_cube a
  constructor
  · rfl
  · simp
    exact perfect_cube_correct a