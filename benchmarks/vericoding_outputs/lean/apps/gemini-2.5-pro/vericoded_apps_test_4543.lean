import Mathlib
-- <vc-preamble>
def natSqrt (n : Nat) : Nat :=
  if n = 0 then 0
  else
    let rec helper (i : Nat) (bound : Nat) : Nat :=
      if bound = 0 then i
      else if i * i ≤ n then
        if (i + 1) * (i + 1) > n then i
        else helper (i + 1) (bound - 1)
      else i
    helper 0 (n + 1)

def Sqrt (n : Int) : Int :=
  if n < 0 then 0 else
  let nat_n := Int.natAbs n
  Int.ofNat (natSqrt nat_n)

def IsPerfectSquare (n : Int) : Prop :=
  n ≥ 0 ∧ (Sqrt n) * (Sqrt n) = n

def IntToString (n : Int) : String :=
  toString n

def StringToInt (s : String) : Int :=
  s.toInt?.getD 0

@[reducible, simp]
def solve_precond (a b : Int) : Prop :=
  a ≥ 1 ∧ a ≤ 100 ∧ b ≥ 1 ∧ b ≤ 100
-- </vc-preamble>

-- <vc-helpers>
instance (n : Int) : Decidable (IsPerfectSquare n) := by
  unfold IsPerfectSquare
  infer_instance
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (_ : solve_precond a b) : String :=
  let a_str := IntToString a
  let b_str := IntToString b
  let concat_str := a_str ++ b_str
  let concat_num := StringToInt concat_str
  if IsPerfectSquare concat_num then
    "Yes"
  else
    "No"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result : String) (_ : solve_precond a b) : Prop :=
  (result = "Yes" ∨ result = "No") ∧
  (let a_str := IntToString a
   let b_str := IntToString b
   let concat_str := a_str ++ b_str
   let concat_num := StringToInt concat_str
   (result = "Yes" ↔ IsPerfectSquare concat_num))

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  dsimp [solve, solve_postcond]
  split_ifs with h
  all_goals simp_all [h]
-- </vc-theorems>
