-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def set_of_seq {T : Type} [Inhabited T] (s : Array T) : List T :=
sorry

def swap {T : Type} [Inhabited T] (a : Array T) (i j : Int) : Array T :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem swap_spec {T : Type} [Inhabited T] (a : Array T) (i j : Int) :
0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < a.size →
let result := swap a i j
result[i.toNat]! = a[j.toNat]! ∧
result[j.toNat]! = a[i.toNat]! ∧
(∀ m : Nat, m < a.size ∧ m ≠ i.toNat ∧ m ≠ j.toNat → result[m]! = a[m]!) :=
sorry
-- </vc-theorems>