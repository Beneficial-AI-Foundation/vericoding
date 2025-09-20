-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD : Nat := 1000000000

def compute_steady_tables (n m : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem steady_tables_in_range (n m : Nat) (h1 : n > 0) (h2 : m > 0) :
  compute_steady_tables n m < MOD :=
  sorry

theorem steady_tables_base_case :
  compute_steady_tables 1 1 = 2 :=
  sorry

theorem steady_tables_ge_rows (n m : Nat) (h1 : n > 0) (h2 : m > 0) :
  compute_steady_tables n m ≥ n :=
  sorry

theorem steady_tables_ge_cols (n m : Nat) (h1 : n > 0) (h2 : m > 0) :
  compute_steady_tables n m ≥ m :=
  sorry

theorem steady_tables_square (n : Nat) (h : n > 0) :
  compute_steady_tables n n ≥ n * n :=
  sorry
-- </vc-theorems>