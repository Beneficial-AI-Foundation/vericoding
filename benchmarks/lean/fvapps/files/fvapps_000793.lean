-- <vc-preamble>
def list_min (l : List Int) : Int :=
  match l with
  | [] => 0
  | (x::xs) => List.foldl min x xs

def list_max (l : List Int) : Int :=
  match l with
  | [] => 0
  | (x::xs) => List.foldl max x xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def compute_cost (x : Int) (k : Nat) (arr : List Int) : Int := sorry

def find_min_x (n k : Nat) (arr : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_x_is_int {n k : Nat} {arr : List Int} (h : arr.length > 0)
  (h1 : k > 0) (h2 : k ≤ 5) :
  ∃ (y : Int), find_min_x n k arr = y :=
sorry

theorem find_min_x_in_range {n k : Nat} {arr : List Int} (h : arr.length > 0)
  (h1 : k > 0) (h2 : k ≤ 5) :
  find_min_x n k arr ≥ (list_min arr - n) ∧
  find_min_x n k arr ≤ (list_max arr + n) :=
sorry

theorem find_min_x_order_invariant {n k : Nat} {arr : List Int} (h : arr.length > 0)
  (h1 : k > 0) (h2 : k ≤ 5) :
  find_min_x n k arr = find_min_x n k arr.reverse :=
sorry

theorem find_min_x_local_optimum {n k : Nat} {arr : List Int}
  (h : arr.length ≥ 3) (h1 : k > 0) (h2 : k ≤ 3) :
  let x := find_min_x n k arr
  let cost := compute_cost x k arr
  let nearby_costs := [compute_cost (x-2) k arr, compute_cost (x-1) k arr,
                      compute_cost (x+1) k arr, compute_cost (x+2) k arr]
  ∀ c ∈ nearby_costs, c ≥ cost * (9/10) :=
sorry
-- </vc-theorems>