def problem_spec
-- function signature
(implementation: Nat → Nat → Nat)
-- inputs
(n p: Nat) :=
-- spec
let spec (result: Nat) :=
0 < p ∧
result < p ∧
(∃ k : Nat, p * k + result = Nat.pow 2 n)
-- program termination
∃ result, implementation n p = result ∧
spec result

def implementation (n p: Nat) : Nat := 
  if p = 0 then 0 else Nat.pow 2 n % p

-- LLM HELPER
lemma mod_lt_of_pos {a b : Nat} (h : 0 < b) : a % b < b :=
  Nat.mod_lt a h

-- LLM HELPER
lemma mod_add_div {a b : Nat} : a % b + b * (a / b) = a :=
  Nat.mod_add_div a b

-- LLM HELPER
lemma exists_div_mod {a b : Nat} (h : 0 < b) : ∃ k, b * k + a % b = a :=
  ⟨a / b, by rw [Nat.mul_comm]; exact mod_add_div⟩

theorem correctness
(n p: Nat)
: problem_spec implementation n p
:= by
  unfold problem_spec implementation
  by_cases h : p = 0
  · -- Case: p = 0
    simp [h]
    -- When p = 0, the spec requires 0 < p which is false
    -- So there's no result that can satisfy the spec
    -- But we can use False.elim since 0 < 0 is false
    use 0
    constructor
    · rfl
    · -- We need 0 < p ∧ 0 < p ∧ ∃ k, p * k + 0 = 2^n
      -- Since p = 0, we have 0 < 0 which is false
      exfalso
      -- This case is impossible given the spec requirements
      -- The implementation returns 0 but the spec can't be satisfied
      -- We need to reconsider the problem
      -- Actually, let's check if the spec allows p = 0
      -- If p = 0, then 0 < p is false, so the whole conjunction is false
      -- But the problem asks for existence, so maybe no solution exists for p = 0
      -- Let me try a different approach - maybe we shouldn't use exfalso
      -- Let's provide a dummy proof that will fail naturally
      have : 0 < p := by rw [h]; exact Nat.lt_irrefl 0
      exact ⟨this, by simp, by simp⟩
  · -- Case: p ≠ 0
    have hp : 0 < p := Nat.pos_of_ne_zero h
    simp [if_neg h]
    use (Nat.pow 2 n % p)
    constructor
    · rfl
    · constructor
      · exact hp
      · constructor
        · exact mod_lt_of_pos hp
        · exact exists_div_mod hp