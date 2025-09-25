-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_graph_direction (n m : Nat) (edges : List (Nat × Nat × Nat)) : String := sorry

def split_lines (s : String) : List String := s.split (· = '\n')
-- </vc-definitions>

-- <vc-theorems>
theorem output_format {n m : Nat} {edges : List (Nat × Nat × Nat)}
  (h_valid_n : n ≥ 2)
  (h_valid_m : m ≥ 1 ∧ m ≤ n * (n-1) / 2)
  (h_no_self_loops : ∀ e ∈ edges, e.2.1 ≠ e.2.2) :
  let result := solve_graph_direction n m edges
  let lines := split_lines result
  (lines ≠ [] ∧ (lines.head! = "YES" ∨ lines.head! = "NO")) ∧
  (lines.head! = "YES" →
    ∀ l ∈ lines.tail,
      ∃ u v : Nat,
      u ≥ 1 ∧ u ≤ n ∧ v ≥ 1 ∧ v ≤ n ∧ u ≠ v) := sorry

theorem directed_edges_count {n m : Nat} {edges : List (Nat × Nat × Nat)} 
  (h_valid_n : n ≥ 2)
  (h_valid_m : m ≥ 1 ∧ m ≤ n * (n-1) / 2)
  (h_no_self_loops : ∀ e ∈ edges, e.2.1 ≠ e.2.2) :
  let result := solve_graph_direction n m edges
  let lines := split_lines result
  lines.head! = "YES" →
  lines.length = m + 1 := sorry
-- </vc-theorems>