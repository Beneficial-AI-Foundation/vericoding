-- <vc-preamble>
@[reducible, simp]
def nthUglyNumber_precond (n : Nat) : Prop :=
  n > 0
-- </vc-preamble>

-- <vc-helpers>
def nextUgly (seq : List Nat) (c2 c3 c5 : Nat) : (Nat × Nat × Nat × Nat) :=
  let i2 := seq[c2]! * 2
  let i3 := seq[c3]! * 3
  let i5 := seq[c5]! * 5
  let next := min i2 (min i3 i5)
  let c2' := if next = i2 then c2 + 1 else c2
  let c3' := if next = i3 then c3 + 1 else c3
  let c5' := if next = i5 then c5 + 1 else c5
  (next, c2', c3', c5')
-- </vc-helpers>

-- <vc-definitions>
def nthUglyNumber (n : Nat) (h_precond : nthUglyNumber_precond (n)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def divideOut : Nat → Nat → Nat
  | n, p =>
    if h : p > 1 ∧ n > 0 ∧ n % p = 0 then
      have : n / p < n := by
        apply Nat.div_lt_self
        · exact h.2.1  -- n > 0
        · exact Nat.lt_of_succ_le (Nat.succ_le_of_lt h.1)  -- 1 < p, so 2 ≤ p
      divideOut (n / p) p
    else n
termination_by n p => n

def isUgly (x : Nat) : Bool :=
  if x = 0 then
    false
  else
    let n1 := divideOut x 2
    let n2 := divideOut n1 3
    let n3 := divideOut n2 5
    n3 = 1
@[reducible, simp]
def nthUglyNumber_postcond (n : Nat) (result: Nat) (h_precond : nthUglyNumber_precond (n)) : Prop :=
  isUgly result = true ∧
  ((List.range (result)).filter (fun i => isUgly i)).length = n - 1

theorem nthUglyNumber_spec_satisfied (n: Nat) (h_precond : nthUglyNumber_precond (n)) :
    nthUglyNumber_postcond (n) (nthUglyNumber (n) h_precond) h_precond := by
  sorry
-- </vc-theorems>