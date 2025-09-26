import Mathlib
-- <vc-preamble>
def pos1 (a b c : Int) : Int :=
  if a ≤ b ∧ a ≤ c then a
  else if b ≤ a ∧ b ≤ c then b
  else c

def pos2 (a b c : Int) : Int :=
  if a ≤ b ∧ a ≤ c then
    if b ≤ c then b else c
  else if b ≤ a ∧ b ≤ c then
    if a ≤ c then a else c
  else
    if a ≤ b then a else b

def pos3 (a b c : Int) : Int :=
  if a ≤ b ∧ a ≤ c then
    if b ≤ c then c else b
  else if b ≤ a ∧ b ≤ c then
    if a ≤ c then c else a
  else
    if a ≤ b then b else a

@[reducible, simp]
def solve_precond (a b c d : Int) : Prop :=
  1 ≤ a ∧ a ≤ 1000000000 ∧
  1 ≤ b ∧ b ≤ 1000000000 ∧
  1 ≤ c ∧ c ≤ 1000000000 ∧
  1 ≤ d ∧ d ≤ 1000000000
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma pos1_is_min (a b c : Int) : pos1 a b c = min a (min b c) := by
  unfold pos1
  split_ifs with h1 h2
  · simp [min_def]
    omega
  · simp [min_def]
    omega
  · push_neg at h1 h2
    simp [min_def]
    omega

-- LLM HELPER
lemma pos2_is_mid (a b c : Int) : 
    pos2 a b c = max (min a b) (max (min a c) (min b c)) := by
  unfold pos2
  split_ifs with h1 h2 h3 h4 h5 h6
  all_goals {
    simp [min_def, max_def]
    split_ifs <;> omega
  }

-- LLM HELPER  
lemma pos3_is_max (a b c : Int) : pos3 a b c = max a (max b c) := by
  unfold pos3
  split_ifs with h1 h2 h3 h4 h5 h6
  all_goals {
    simp [max_def]
    split_ifs <;> omega
  }
-- </vc-helpers>

-- <vc-definitions>
def solve (a b c d : Int) (h_precond : solve_precond a b c d) : Int :=
  let min_val := pos1 a b c
  let mid_val := pos2 a b c 
  let max_val := pos3 a b c
  let diff1 := mid_val - min_val
  let diff2 := max_val - mid_val
  (if d > diff1 then d - diff1 else 0) + (if d > diff2 then d - diff2 else 0)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b c d : Int) (result: Int) (h_precond : solve_precond a b c d) : Prop :=
  result ≥ 0 ∧
  result = (if d > (pos2 a b c - pos1 a b c) then d - (pos2 a b c - pos1 a b c) else 0) +
           (if d > (pos3 a b c - pos2 a b c) then d - (pos3 a b c - pos2 a b c) else 0)

theorem solve_spec_satisfied (a b c d : Int) (h_precond : solve_precond a b c d) :
    solve_postcond a b c d (solve a b c d h_precond) h_precond := by
  unfold solve solve_postcond
  constructor
  · -- Prove result ≥ 0
    simp only []
    split_ifs <;> omega
  · -- Prove the equality
    -- The let bindings in solve match exactly the expressions in postcond
    rfl
-- </vc-theorems>
