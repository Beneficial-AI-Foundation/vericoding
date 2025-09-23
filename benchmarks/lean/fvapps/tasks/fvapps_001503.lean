-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Nat) : List Nat :=
sorry

def cell_advance_hero1 (row col n m k : Nat) : (Nat × Nat) :=
sorry

def cell_advance_hero2 (row col n m k : Nat) : (Nat × Nat) :=
sorry

def find_destroyed_cells (advance : Nat → Nat → Nat → Nat → Nat → (Nat × Nat)) (n m k : Nat) : List (Nat × Nat) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_output_range {n m : Nat} (h1 : n > 0) (h2 : m > 0) :
  let result := solve n m;
  List.length result = n * m ∧
  ∀ x, x ∈ result → 1 ≤ x ∧ x ≤ n * m * 2 := by
  sorry

theorem solve_first_last {n m : Nat} (h1 : n > 0) (h2 : m > 0) :
  let result := solve n m;
  List.head! result ≥ List.getLast! result ∧
  List.getLast! result ≥ 1 := by
  sorry

theorem cell_advance_hero1_bounds {row col n m k : Nat} (h1 : n > 0) (h2 : m > 0) :
  let result := cell_advance_hero1 row col n m k;
  1 ≤ result.2 ∧ result.2 ≤ m := by
  sorry

theorem cell_advance_hero2_bounds {row col n m k : Nat} (h1 : n > 0) (h2 : m > 0) :
  let result := cell_advance_hero2 row col n m k;
  1 ≤ result.1 ∧ result.1 ≤ n := by
  sorry

theorem destroyed_cells_bounds {n m k : Nat} (h1 : n > 0) (h2 : m > 0) :
  let cells1 := find_destroyed_cells cell_advance_hero1 n m k;
  let cells2 := find_destroyed_cells cell_advance_hero2 n m k;
  (∀ p ∈ cells1, 1 ≤ p.1 ∧ p.1 ≤ n ∧ 1 ≤ p.2 ∧ p.2 ≤ m) ∧
  (∀ p ∈ cells2, 1 ≤ p.1 ∧ p.1 ≤ n ∧ 1 ≤ p.2 ∧ p.2 ≤ m) := by
  sorry

theorem destroyed_cells_start {n m k : Nat} (h1 : n > 0) (h2 : m > 0) :
  let cells1 := find_destroyed_cells cell_advance_hero1 n m k;
  let cells2 := find_destroyed_cells cell_advance_hero2 n m k;
  (1, 1) ∈ cells1 ∧ (1, 1) ∈ cells2 := by
  sorry
-- </vc-theorems>