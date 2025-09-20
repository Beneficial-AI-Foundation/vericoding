-- <vc-preamble>
def list_sum (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | x::rest => x + list_sum rest
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_valid_partition (n : Nat) (a b : Int) (xs : List Int) (result : Option (List Nat)) : Bool := sorry

def solve_partition (n : Nat) (a b : Int) (xs : List Int) : Option (List Nat) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_partition_correct (n : Nat) (a b : Int) (xs : List Int) :
  let result := solve_partition n a b xs
  match result with
  | none => True
  | some partition =>

    partition.length = n ∧

    (∀ x ∈ partition, x = 0 ∨ x = 1) ∧

    let groups := List.zipWith (λ (x : Int) (g : Nat) => if g = 0 then some x else none) xs partition
    let sum0 := list_sum (groups.filterMap id)
    let groups1 := List.zipWith (λ (x : Int) (g : Nat) => if g = 1 then some x else none) xs partition
    let sum1 := list_sum (groups1.filterMap id)
    (sum0 = a ∨ sum0 = b) ∧ (sum1 = a ∨ sum1 = b) :=
sorry

theorem solve_partition_same_sum (n : Nat) (a : Int) (xs : List Int)
  (h1 : n ≥ 2)
  (h2 : a ≥ 3)
  (h3 : xs.length = n)
  (h4 : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 5)
  (h5 : ∀ x ∈ xs, ∃ y ∈ xs, x + y = a) :
  match solve_partition n a a xs with
  | none => True
  | some partition => ∀ g ∈ partition, g = 0 :=
sorry
-- </vc-theorems>