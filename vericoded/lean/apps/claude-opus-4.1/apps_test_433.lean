import Mathlib
-- <vc-preamble>
def ValidInput (n a b : Int) : Prop :=
  n ≥ 1 ∧ 1 ≤ a ∧ a ≤ n ∧ -100 ≤ b ∧ b ≤ 100

def FinalEntrance (n a b : Int) (h : ValidInput n a b) : Int :=
  ((a - 1 + b) % n + n) % n + 1

def ValidOutput (result n : Int) : Prop :=
  1 ≤ result ∧ result ≤ n

@[reducible, simp]
def solve_precond (n a b : Int) : Prop :=
  ValidInput n a b
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma mod_add_mod_eq (a b n : Int) (hn : n > 0) : ((a % n + n) % n) = (a % n + n) % n := by
  rfl

-- LLM HELPER
lemma final_entrance_range (n a b : Int) (h : ValidInput n a b) :
    1 ≤ FinalEntrance n a b h ∧ FinalEntrance n a b h ≤ n := by
  unfold FinalEntrance ValidInput at *
  have hn : n ≥ 1 := h.1
  have ha : 1 ≤ a ∧ a ≤ n := ⟨h.2.1, h.2.2.1⟩
  have hb : -100 ≤ b ∧ b ≤ 100 := ⟨h.2.2.2.1, h.2.2.2.2⟩
  -- The result is ((a - 1 + b) % n + n) % n + 1
  -- This ensures the result is in [1, n]
  have mod_range : 0 ≤ ((a - 1 + b) % n + n) % n ∧ ((a - 1 + b) % n + n) % n < n := by
    constructor
    · apply Int.emod_nonneg
      linarith
    · apply Int.emod_lt_of_pos
      linarith
  constructor
  · -- 1 ≤ result
    linarith [mod_range.1]
  · -- result ≤ n  
    linarith [mod_range.2, hn]
-- </vc-helpers>

-- <vc-definitions>
def solve (n a b : Int) (h_precond : solve_precond n a b) : Int :=
  FinalEntrance n a b h_precond
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n a b : Int) (result : Int) (h_precond : solve_precond n a b) : Prop :=
  ValidOutput result n ∧ result = FinalEntrance n a b h_precond

theorem solve_spec_satisfied (n a b : Int) (h_precond : solve_precond n a b) :
    solve_postcond n a b (solve n a b h_precond) h_precond := by
  unfold solve_postcond solve ValidOutput
  constructor
  · -- Prove ValidOutput
    exact final_entrance_range n a b h_precond
  · -- Prove equality
    rfl
-- </vc-theorems>
