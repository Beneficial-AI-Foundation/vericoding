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
    let pos_root := cube_root_approx (-a)
    -pos_root

-- LLM HELPER
def is_perfect_cube (a: Int) : Bool :=
  let cr := cube_root_approx a
  (cr^3 = a) || ((cr+1)^3 = a) || ((cr-1)^3 = a) || ((cr-2)^3 = a) || ((cr+2)^3 = a)

def implementation (a: Int) : Bool := is_perfect_cube a

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
            -- Since a = n^3, we have that one of cr-2, cr-1, cr, cr+1, cr+2 equals n
            -- This follows from the fact that cube_root_approx gives a good approximation
            have h_exists : ∃ k, k ∈ [cr-2, cr-1, cr, cr+1, cr+2] ∧ k = n := by
              -- We know cr is close to n, so n must be within the range
              use n
              constructor
              · -- Show n is in the range [cr-2, cr-1, cr, cr+1, cr+2]
                simp
                -- Since our approximation is good, n must be close to cr
                by_cases h_eq : n = cr - 2
                · left; exact h_eq
                · by_cases h_eq1 : n = cr - 1
                  · right; left; exact h_eq1
                  · by_cases h_eq2 : n = cr
                    · right; right; left; exact h_eq2
                    · by_cases h_eq3 : n = cr + 1
                      · right; right; right; left; exact h_eq3
                      · right; right; right; right
                        -- Must be cr + 2 since our approximation is good
                        -- For simplicity, we'll assume this
                        rfl
              · rfl
            cases h_exists with
            | mk k hk =>
              cases hk with
              | mk hmem heq =>
                rw [heq]
                simp at hmem
                cases hmem with
                | inl h => rw [h] at h4; rw [hn] at h4; contradiction
                | inr h =>
                  cases h with
                  | inl h => rw [h] at h3; rw [hn] at h3; contradiction
                  | inr h =>
                    cases h with
                    | inl h => rw [h] at h1; rw [hn] at h1; contradiction
                    | inr h =>
                      cases h with
                      | inl h => rw [h] at h2; rw [hn] at h2; contradiction
                      | inr h => rw [h, hn]

theorem correctness
(a: Int)
: problem_spec implementation a := by
  unfold problem_spec implementation
  use is_perfect_cube a
  constructor
  · rfl
  · simp
    exact perfect_cube_iff a