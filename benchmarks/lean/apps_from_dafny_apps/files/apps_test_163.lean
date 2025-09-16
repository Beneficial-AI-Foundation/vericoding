-- <vc-preamble>
def ValidInput (n k : Int) (s : String) : Prop :=
  n ≥ 2 ∧
  1 ≤ k ∧ k < n ∧
  s.length = n.natAbs ∧
  (∃ i : Nat, i < s.length ∧ s.data[i]! = 'G') ∧
  (∃ i : Nat, i < s.length ∧ s.data[i]! = 'T') ∧
  (∀ i : Nat, i < s.length → s.data[i]! ∈ ['G', 'T', '.', '#']) ∧
  (∀ i j : Nat, i < j ∧ j < s.length ∧ s.data[i]! = 'G' → s.data[j]! ≠ 'G') ∧
  (∀ i j : Nat, i < j ∧ j < s.length ∧ s.data[i]! = 'T' → s.data[j]! ≠ 'T')

def FindFirstGOrT (s : String) : Int :=
  sorry

def CanReachTarget (s : String) (k : Int) : Prop :=
  k > 0 →
  ∃ start : Nat, 
    start < s.length ∧ 
    s.data[start]! ∈ ['G', 'T'] ∧
    (∀ j : Nat, j < start → s.data[j]! ∉ ['G', 'T']) ∧
    (∃ final : Nat, 
        start < final ∧ final < s.length ∧
        s.data[final]! ∈ ['G', 'T'] ∧
        (final - start) % k.natAbs = 0 ∧
        (∀ pos : Nat, start < pos ∧ pos < final ∧ (pos - start) % k.natAbs = 0 → s.data[pos]! ∉ ['G', 'T', '#'])
    )

@[reducible, simp]
def solve_precond (n k : Int) (s : String) : Prop :=
  ValidInput n k s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (s : String) (h_precond : solve_precond n k s) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (s : String) (result : String) (h_precond : solve_precond n k s) : Prop :=
  (result = "YES" ∨ result = "NO") ∧
  (result = "YES" ↔ CanReachTarget s k)

theorem solve_spec_satisfied (n k : Int) (s : String) (h_precond : solve_precond n k s) :
    solve_postcond n k s (solve n k s h_precond) h_precond := by
  sorry
-- </vc-theorems>
