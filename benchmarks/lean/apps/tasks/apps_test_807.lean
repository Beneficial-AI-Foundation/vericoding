-- <vc-preamble>

def ValidInput (n c : Int) (prices : List Int) : Prop :=
  n ≥ 2 ∧ prices.length = n ∧ c ≥ 0 ∧
  (∀ i, 0 ≤ i ∧ i < prices.length → prices[i]! ≥ 0)

def ProfitForDay (prices : List Int) (day c : Int) : Int :=
  if 0 ≤ day ∧ day + 1 < prices.length then
    prices[day.natAbs]! - prices[(day + 1).natAbs]! - c
  else 0

def seq_max (s : List Int) : Int :=
  match s with
  | [] => 0
  | [x] => x
  | x :: xs => max x (seq_max xs)

def MaxPossibleProfit (prices : List Int) (c : Int) : Int :=
  let profits := (List.range (prices.length - 1)).map (fun i => ProfitForDay prices (Int.ofNat i) c)
  if profits.length = 0 then 0 else seq_max profits

def CorrectResult (n c : Int) (prices : List Int) (result : Int) : Prop :=
  ValidInput n c prices →
  (result ≥ 0 ∧
   (result = 0 ↔ (∀ i, 0 ≤ i ∧ i < n - 1 → ProfitForDay prices i c ≤ 0)) ∧
   (result > 0 → (∃ i, 0 ≤ i ∧ i < n - 1 ∧ ProfitForDay prices i c = result)) ∧
   (∀ i, 0 ≤ i ∧ i < n - 1 → ProfitForDay prices i c ≤ result))

@[reducible, simp]
def solve_precond (n c : Int) (prices : List Int) : Prop :=
  ValidInput n c prices
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n c : Int) (prices : List Int) (h_precond : solve_precond n c prices) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n c : Int) (prices : List Int) (result : Int) (h_precond : solve_precond n c prices) : Prop :=
  CorrectResult n c prices result

theorem solve_spec_satisfied (n c : Int) (prices : List Int) (h_precond : solve_precond n c prices) :
    solve_postcond n c prices (solve n c prices h_precond) h_precond := by
  sorry
-- </vc-theorems>