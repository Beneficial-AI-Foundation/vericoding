import Mathlib
-- <vc-preamble>
def max_prefix (s : List Int) (i : Nat) : Int :=
  if h : i < s.length then
    if i = 0 then s[0]!
    else if s[i]! > max_prefix s (i - 1) then s[i]!
    else max_prefix s (i - 1)
  else 0
termination_by i

def max_seq (s : List Int) : Int :=
  if h : s.length > 0 then
    if s.length = 1 then s[0]!
    else if s[s.length - 1]! > max_seq (s.dropLast) then s[s.length - 1]!
    else max_seq (s.dropLast)
  else 0
termination_by s.length

def max_expression (n : Int) (p : Int) (q : Int) (r : Int) (a : List Int) : Int :=
  if h : n > 0 ∧ a.length = n.toNat then
    let s1 := List.range n.toNat |>.map (fun i => a[i]! * p)
    let s2 := List.range n.toNat |>.map (fun i => max_prefix s1 i + a[i]! * q)
    let s3 := List.range n.toNat |>.map (fun i => max_prefix s2 i + a[i]! * r)
    max_seq s3
  else 0

def ValidInput (n : Int) (a : List Int) : Prop :=
  n > 0 ∧ a.length = n.toNat

@[reducible, simp]
def solve_precond (n : Int) (p : Int) (q : Int) (r : Int) (a : List Int) : Prop :=
  ValidInput n a
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (p : Int) (q : Int) (r : Int) (a : List Int) (h_precond : solve_precond n p q r a) : Int :=
  max_expression n p q r a
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (p : Int) (q : Int) (r : Int) (a : List Int) (result : Int) (h_precond : solve_precond n p q r a) : Prop :=
  result = max_expression n p q r a

theorem solve_spec_satisfied (n : Int) (p : Int) (q : Int) (r : Int) (a : List Int) (h_precond : solve_precond n p q r a) :
    solve_postcond n p q r a (solve n p q r a h_precond) h_precond := by
  simp [solve, solve_postcond]
-- </vc-theorems>
