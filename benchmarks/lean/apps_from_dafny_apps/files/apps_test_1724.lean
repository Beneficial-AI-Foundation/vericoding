-- <vc-preamble>
def isBinaryString (s : String) : Prop :=
  ∀ i : Nat, i < s.length → s.data[i]! = '0' ∨ s.data[i]! = '1'

def pow (base : Int) (exp : Nat) : Int :=
  match exp with
  | 0 => 1 
  | n + 1 => base * pow base n

def binaryStringToInt (s : String) : Int :=
  if s.isEmpty then 0 
  else (if s.data[0]! = '1' then 1 else 0) * pow 2 (s.length - 1) + binaryStringToInt (s.drop 1)
  termination_by s.length
  decreasing_by
    simp [String.drop, String.length]
    sorry

def f (a : List Int) (x : Int) (n : Nat) : Int :=
  match n with
  | 0 => 0
  | n + 1 => 
    let bit := if x / pow 2 n % 2 = 1 then 1 else 0
    (if bit = 1 then a[n]! else 0) + f (a.take n) (x % pow 2 n) n

@[reducible, simp]
def solve_precond (n : Int) (a : List Int) (k : String) : Prop :=
  n ≥ 1 ∧ a.length = n.natAbs ∧ k.length = n.natAbs ∧ 
  (∀ i : Nat, i < n.natAbs → a[i]! ≥ 0) ∧
  isBinaryString k
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (a : List Int) (k : String) (h_precond : solve_precond n a k) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (a : List Int) (k : String) (result: Int) (h_precond : solve_precond n a k) : Prop :=
  result ≥ 0 ∧ 
  (∃ x : Int, 0 ≤ x ∧ x ≤ binaryStringToInt k ∧ result = f a x n.natAbs) ∧
  (∀ x : Int, 0 ≤ x ∧ x ≤ binaryStringToInt k → f a x n.natAbs ≤ result)

theorem solve_spec_satisfied (n : Int) (a : List Int) (k : String) (h_precond : solve_precond n a k) :
    solve_postcond n a k (solve n a k h_precond) h_precond := by
  sorry
-- </vc-theorems>
