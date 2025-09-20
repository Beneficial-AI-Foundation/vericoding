-- <vc-preamble>
def sum_list : List Nat → Nat
  | [] => 0
  | (x::xs) => x + sum_list xs

def list_get (xs : List Nat) (i : Nat) : Option Nat :=
  match xs, i with
  | [], _ => none
  | (x::_), 0 => some x
  | (_::xs), n+1 => list_get xs n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def make_grid (n m : Nat) (house_coords : List (Nat × Nat)) : List String :=
sorry

def solve_house_distances (n m : Nat) (grid : List String) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem house_distances_properties
  (n m : Nat) (coords : List (Nat × Nat))
  (h_n : n > 0) (h_m : m > 0)
  (h_coords : coords.length ≥ 2)
  (h_valid : ∀ (p : Nat × Nat), p ∈ coords → p.1 < n ∧ p.2 < m)
  (h_unique : ∀ (p q : Nat × Nat), p ∈ coords → q ∈ coords → p = q ∨ p ≠ q) :
  let result := solve_house_distances n m (make_grid n m coords);
  let num_pairs := (coords.length * (coords.length - 1)) / 2;
  result.length = n + m - 2 ∧
  (∀ x ∈ result, x ≥ 0) ∧
  sum_list result = num_pairs ∧
  (sum_list result > 0 →
   ∀ i x, i < result.length → list_get result i = some x → x > 0 → i + 1 ≥ 1) :=
sorry

theorem minimal_case
  (n m : Nat)
  (h_n : n ≥ 2) (h_m : m ≥ 2) :
  let corner_houses := [(0,0), (n-1,m-1)];
  let result := solve_house_distances n m (make_grid n m corner_houses);
  list_get result (n+m-3) = some 1 ∧
  sum_list result = 1 :=
sorry
-- </vc-theorems>