-- <vc-preamble>
def is_tandem_repeat (s : List Char) : Bool :=
  if s.length % 2 ≠ 0 then false
  else
    let half_len := s.length / 2
    let first_half := s.take half_len
    let second_half := s.drop half_len
    (List.range half_len).all fun i =>
      first_half.get! i = '*' ∨ second_half.get! i = '*' ∨ first_half.get! i = second_half.get! i

@[reducible, simp]
def solve_precond (s : String) (k : Int) : Prop :=
  k ≥ 1 ∧ s.length ≥ 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (k : Int) (h_precond : solve_precond s k) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (k : Int) (result : Int) (h_precond : solve_precond s k) : Prop :=
  result ≥ 0 ∧
  result % 2 = 0 ∧
  result ≤ s.length + k ∧
  (∀ i n, 0 ≤ i ∧ i < s.length + k ∧ 2 ≤ n ∧ n ≤ s.length + k - i ∧ n % 2 = 0 ∧
    is_tandem_repeat ((s.data ++ List.replicate k.natAbs '*').drop i.natAbs |>.take n.natAbs) → n ≤ result) ∧
  (result = 0 → ∀ i n, 0 ≤ i ∧ i < s.length + k ∧ 2 ≤ n ∧ n ≤ s.length + k - i ∧ n % 2 = 0 →
    ¬is_tandem_repeat ((s.data ++ List.replicate k.natAbs '*').drop i.natAbs |>.take n.natAbs)) ∧
  (result > 0 → ∃ i n, 0 ≤ i ∧ i < s.length + k ∧ 2 ≤ n ∧ n ≤ s.length + k - i ∧ n % 2 = 0 ∧
    is_tandem_repeat ((s.data ++ List.replicate k.natAbs '*').drop i.natAbs |>.take n.natAbs) ∧ n = result)

theorem solve_spec_satisfied (s : String) (k : Int) (h_precond : solve_precond s k) :
    solve_postcond s k (solve s k h_precond) h_precond := by
  sorry
-- </vc-theorems>