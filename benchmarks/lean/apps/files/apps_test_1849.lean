-- <vc-preamble>
def MOD : Int := 998244353

def pow (base : Int) (exp : Int) (mod : Int) : Int :=
  if exp = 0 then 1 % mod
  else if exp = 1 then base % mod
  else (base ^ exp.natAbs) % mod

def ValidInput (n : Int) : Prop :=
  n ≥ 1

def BlockCountFormula (n : Int) (i : Int) : Int :=
  if n ≥ 1 ∧ 1 ≤ i ∧ i ≤ n then
    if i = n then 10
    else 
      ((2 * 9 * pow 10 (n - i - 1) MOD * 10) + 
       (if i < n - 1 then ((n - 1 - i) * 9 * 9 * pow 10 (n - i - 2) MOD * 10) else 0)) % MOD
  else 0

def ValidResult (result : List Int) (n : Int) : Prop :=
  n ≥ 1 →
  result.length = Int.natAbs n ∧
  (∀ k, 0 ≤ k ∧ k < n → k ≥ 0 ∧ Int.natAbs k < result.length → 0 ≤ result[Int.natAbs k]! ∧ result[Int.natAbs k]! < MOD) ∧
  (n ≥ 1 → n - 1 ≥ 0 ∧ Int.natAbs (n - 1) < result.length → result[Int.natAbs (n - 1)]! = 10) ∧
  (∀ i, 0 ≤ i ∧ i < n - 1 → i ≥ 0 ∧ Int.natAbs i < result.length → result[Int.natAbs i]! = BlockCountFormula n (i + 1))

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : List Int) (h_precond : solve_precond n) : Prop :=
  ValidResult result n

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>