-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Command := String

def optimize_calpas (cmds : List Command) : Nat × List Command :=
  sorry

/- Result has at most 3 commands -/
-- </vc-definitions>

-- <vc-theorems>
theorem optimize_length_bound {cmds : List Command} :
  let (n, optimized) := optimize_calpas cmds
  n ≤ 3 ∧ optimized.length = n := by
  sorry

/- Commands are properly formatted -/

theorem optimize_valid_commands {cmds : List Command} :
  let (n, optimized) := optimize_calpas cmds
  ∀ cmd ∈ optimized,
    (cmd.get 0 = '|' ∨ cmd.get 0 = '&' ∨ cmd.get 0 = '^') := by
  sorry

/- Each operation appears at most once -/ 

theorem optimize_unique_ops {cmds : List Command} :
  let (n, optimized) := optimize_calpas cmds
  let ops := optimized.map (fun cmd => cmd.get 0)
  ops.length = ops.eraseDups.length := by
  sorry

/- Operations appear in correct order: |, ^, & -/

theorem optimize_op_ordering {cmds : List Command} :
  let (n, optimized) := optimize_calpas cmds
  let ops := optimized.map (fun cmd => cmd.get 0)
  ∀ i j, i < j → j < ops.length →
    let i' : Fin ops.length := ⟨i, by sorry⟩
    let j' : Fin ops.length := ⟨j, by sorry⟩
    ((ops.get i' = '|' ∧ ops.get j' = '^') →
     (ops.get i' = '|' ∧ ops.get j' = '&') →
     (ops.get i' = '^' ∧ ops.get j' = '&') →
     i < j) := by
  sorry
-- </vc-theorems>