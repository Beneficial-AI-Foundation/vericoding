-- <vc-preamble>
def ValidTriple (a b c N K : Int) (hK : K ≥ 1) : Prop :=
  1 ≤ a ∧ a ≤ N ∧ 1 ≤ b ∧ b ≤ N ∧ 1 ≤ c ∧ c ≤ N ∧
  (a + b) % K = 0 ∧ (b + c) % K = 0 ∧ (c + a) % K = 0

def CountValidTriples (N K : Int) (hN : N ≥ 1) (hK : K ≥ 1) : Int :=
  if K % 2 = 1 then
    let cnt1 := N / K
    cnt1 * cnt1 * cnt1
  else
    let cnt1 := N / K
    let cnt2 := N / K + (if N % K ≥ K / 2 then 1 else 0)
    cnt1 * cnt1 * cnt1 + cnt2 * cnt2 * cnt2

def ValidInput (N K : Int) : Prop :=
  N ≥ 1 ∧ K ≥ 1

def CountDivisibleByK (n K : Int) (hK : K ≥ 1) : Int :=
  if n ≤ 0 then 0 else n / K

def CountWithRemainderHalfK (n K : Int) (hK : K ≥ 1) : Int :=
  if n ≤ 0 then 0 else n / K + (if n % K ≥ K / 2 then 1 else 0)

@[reducible, simp]
def solve_precond (N K : Int) : Prop :=
  ValidInput N K
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (N K : Int) (h_precond : solve_precond N K) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N K : Int) (result : Int) (h_precond : solve_precond N K) : Prop :=
  result ≥ 0 ∧ result = CountValidTriples N K (h_precond.1) (h_precond.2)

theorem solve_spec_satisfied (N K : Int) (h_precond : solve_precond N K) :
    solve_postcond N K (solve N K h_precond) h_precond := by
  sorry
-- </vc-theorems>