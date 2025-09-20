-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def distribute (nodes : Nat) (workload : Nat) : List (List Nat) :=
  sorry

def listMaximum (l : List Nat) : Nat :=
  sorry

def listMinimum (l : List Nat) : Nat :=
  sorry

def listSum (l : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem distribute_length {nodes workload : Nat}
  (h : nodes ≤ workload ∨ workload = 0) :
  (distribute nodes workload).length = nodes :=
sorry
-- </vc-theorems>