-- <vc-preamble>
def listMin (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x::xs => List.foldl min x xs

def listMax (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x::xs => List.foldl max x xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m k : Nat) (arr : List Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_result_in_bounds {n m k : Nat} {arr : List Nat}
  (h1 : arr.length ≥ m) (h2 : m ≤ n) (h3 : arr ≠ []) :
  let result := solve n m k arr
  listMin arr ≤ result ∧ result ≤ listMax arr :=
sorry

theorem solve_k_zero {n m : Nat} {arr : List Nat}
  (h1 : arr.length ≥ m) (h2 : m ≤ n) :
  solve n m 0 arr =
    listMin (List.map
      (fun i => max (arr[i]!) (arr[arr.length - i - 1]!))
      (List.range m)) :=
sorry

theorem solve_k_large {n m k : Nat} {arr : List Nat}
  (h1 : arr.length ≥ m) (h2 : m ≤ n) (h3 : k ≥ m-1) (h4 : m > 0) :
  solve n m k arr =
    listMax (List.map
      (fun i => max (arr[i]!) (arr[arr.length - i - 1]!))
      (List.range m)) :=
sorry

theorem solve_empty_error {n m : Nat} :
  solve n m 0 [] = 0 :=
sorry

theorem solve_negative_k {n m k : Nat} {arr : List Nat}
  (h1 : arr.length ≥ m) (h2 : m ≤ n) :
  solve n m 0 arr = solve n m k arr :=
sorry

theorem solve_very_large_k {n m k : Nat} {arr : List Nat}
  (h1 : arr.length ≥ m) (h2 : m ≤ n) (h3 : k ≥ m-1) :
  solve n m k arr = solve n m (m-1) arr :=
sorry
-- </vc-theorems>