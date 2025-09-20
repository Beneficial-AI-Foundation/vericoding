-- <vc-preamble>
def factorial (n: Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_perms (matrix: List (List Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_perms_single_element :
  count_perms [[1]] = 1 := by
sorry

theorem count_perms_dimensions_preserved {m n: Nat} (matrix: List (List Nat))
  (h1: matrix.length = m)
  (h2: ∀ row ∈ matrix, row.length = n) :
  let result := count_perms matrix

  0 < result ∧

  result ≤ factorial (m * n) := by
sorry

theorem count_perms_all_same {m n: Nat}
  (h1: 0 < m) (h2: 0 < n) :
  let matrix := List.replicate m (List.replicate n 1)
  count_perms matrix = 1 := by
sorry

theorem count_perms_all_different {m n: Nat}
  (h1: 0 < m) (h2: 0 < n) :
  let matrix := List.map (fun i =>
    List.map (fun j => i * n + j + 1) (List.range n)
  ) (List.range m)
  count_perms matrix = factorial (m * n) := by
sorry
-- </vc-theorems>