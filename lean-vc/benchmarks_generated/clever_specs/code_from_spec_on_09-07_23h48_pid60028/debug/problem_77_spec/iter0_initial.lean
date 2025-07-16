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
    Nat.floor (Real.rpow a.natAbs (1/3 : Real))
  else
    -Nat.floor (Real.rpow ((-a).natAbs) (1/3 : Real))

-- LLM HELPER
def is_perfect_cube (a: Int) : Bool :=
  let cr := cube_root_int a
  (cr^3 = a) || ((cr+1)^3 = a) || ((cr-1)^3 = a)

def implementation (a: Int) : Bool := is_perfect_cube a

-- LLM HELPER
lemma cube_root_bounds (a: Int) (h: a ≥ 0) : 
  let cr := cube_root_int a
  cr^3 ≤ a ∧ a < (cr+1)^3 := by
  sorry

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
          sorry
        rw [this, hn]

-- LLM HELPER
lemma perfect_cube_false (a: Int) : 
  is_perfect_cube a = false ↔ ¬∃ n: Int, a = n^3 := by
  rw [←perfect_cube_correct]
  simp

theorem correctness
(a: Int)
: problem_spec implementation a := by
  unfold problem_spec implementation
  simp
  constructor
  · rfl
  · by_cases h: is_perfect_cube a
    · simp [h]
      exact perfect_cube_correct a
    · simp [h]
      exact perfect_cube_false a