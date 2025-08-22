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
def cube_root_approx (a: Int) : Int :=
  if a = 0 then 0
  else if a > 0 then
    -- Find approximate cube root by binary search
    let rec aux (low high : Int) (fuel : Nat) : Int :=
      if fuel = 0 then low
      else if low >= high then low
      else
        let mid := (low + high) / 2
        if mid * mid * mid = a then mid
        else if mid * mid * mid < a then aux (mid + 1) high (fuel - 1)
        else aux low (mid - 1) (fuel - 1)
    aux 0 (a + 1) 100
  else
    -- For negative numbers
    -(cube_root_approx (-a))

-- LLM HELPER
def is_perfect_cube (a: Int) : Bool :=
  let cr := cube_root_approx a
  (cr^3 = a) || ((cr+1)^3 = a) || ((cr-1)^3 = a) || ((cr-2)^3 = a) || ((cr+2)^3 = a)

def implementation (a: Int) : Bool := is_perfect_cube a

-- LLM HELPER
lemma cube_unique (x y : Int) : x^3 = y^3 → x = y := by
  intro h
  by_cases hx : x ≥ 0
  · by_cases hy : y ≥ 0
    · -- Both non-negative
      by_contra h_ne
      wlog h_lt : x < y
      · have h_pow : x^3 < y^3 := by
          exact pow_lt_pow_right (by norm_num) h_lt
        rw [h] at h_pow
        exact lt_irrefl _ h_pow
      · exact this h.symm hy hx h_ne.symm (le_of_not_gt h_lt)
    · -- x ≥ 0, y < 0
      have h_y_neg : y^3 < 0 := by
        have : Odd 3 := by norm_num
        exact pow_neg_of_neg_of_odd hy this
      have h_x_nonneg : x^3 ≥ 0 := by
        exact pow_nonneg hx 3
      rw [h] at h_x_nonneg
      exact not_le.mpr h_y_neg h_x_nonneg
  · by_cases hy : y ≥ 0
    · -- x < 0, y ≥ 0
      have h_x_neg : x^3 < 0 := by
        have : Odd 3 := by norm_num
        exact pow_neg_of_neg_of_odd hx this
      have h_y_nonneg : y^3 ≥ 0 := by
        exact pow_nonneg hy 3
      rw [←h] at h_y_nonneg
      exact not_le.mpr h_x_neg h_y_nonneg
    · -- Both negative
      have h_pos_x : (-x) > 0 := neg_pos.mpr hx
      have h_pos_y : (-y) > 0 := neg_pos.mpr hy
      have h_neg_eq : (-x)^3 = (-y)^3 := by
        rw [neg_pow_odd, neg_pow_odd, h]
        norm_num
      have h_neg_unique : (-x) = (-y) := by
        apply cube_unique
        exact h_neg_eq
      exact neg_inj.mp h_neg_unique

-- LLM HELPER
lemma perfect_cube_iff (a: Int) : 
  is_perfect_cube a = true ↔ ∃ n: Int, a = n^3 := by
  constructor
  · intro h
    unfold is_perfect_cube at h
    simp at h
    let cr := cube_root_approx a
    cases h with
    | inl h1 => use cr; exact h1.symm
    | inr h2 => 
      cases h2 with
      | inl h2 => use cr + 1; exact h2.symm
      | inr h3 =>
        cases h3 with
        | inl h3 => use cr - 1; exact h3.symm
        | inr h4 =>
          cases h4 with
          | inl h4 => use cr - 2; exact h4.symm
          | inr h5 => use cr + 2; exact h5.symm
  · intro ⟨n, hn⟩
    unfold is_perfect_cube
    simp
    let cr := cube_root_approx a
    by_cases h1: cr^3 = a
    · left; exact h1
    · by_cases h2: (cr+1)^3 = a
      · right; left; exact h2
      · by_cases h3: (cr-1)^3 = a
        · right; right; left; exact h3
        · by_cases h4: (cr-2)^3 = a
          · right; right; right; left; exact h4
          · right; right; right; right
            rw [←hn]
            -- Since a = n^3, and our approximation is within 2 of the actual cube root
            -- one of cr-2, cr-1, cr, cr+1, cr+2 must equal n
            have h_eq_cr2 : (cr + 2)^3 = n^3 := by rw [hn]
            have h_n_eq : n = cr + 2 := cube_unique n (cr + 2) h_eq_cr2.symm
            rw [h_n_eq, hn]

theorem correctness
(a: Int)
: problem_spec implementation a := by
  unfold problem_spec implementation
  use is_perfect_cube a
  constructor
  · rfl
  · simp
    exact perfect_cube_iff a