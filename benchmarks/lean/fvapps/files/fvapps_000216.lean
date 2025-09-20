-- <vc-preamble>
def sum (l : List Nat) : Nat :=
  l.foldr (· + ·) 0

def minimum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x::xs => xs.foldr min x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxSatisfied (customers : List Nat) (grumpy : List Nat) (X : Nat) : Nat := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxSatisfied_properties {customers grumpy : List Nat} {X : Nat}
  (h1 : customers.length > 0)
  (h2 : grumpy.length = customers.length)
  (h3 : X > 0)
  (h4 : ∀ x ∈ customers, x ≤ 1000)
  (h5 : ∀ x ∈ grumpy, x ≤ 1) :
  let result := maxSatisfied customers grumpy X
  let base_satisfied := (List.zip customers grumpy).foldr (fun (p : Nat × Nat) acc => 
    if p.2 = 0 then acc + p.1 else acc) 0
  (result ≥ base_satisfied 
  ∧ result ≤ sum customers
  ∧ (grumpy.all (· = 0) → result = sum customers)) := by
  sorry

theorem maxSatisfied_single_element {customers : List Nat} 
  (h1 : customers.length > 0) :
  let grumpy_zeros := List.replicate customers.length 0
  let grumpy_ones := List.replicate customers.length 1
  (maxSatisfied customers grumpy_zeros 1 = sum customers
  ∧ maxSatisfied customers grumpy_ones 1 ≥ minimum customers) := by
  sorry
-- </vc-theorems>