-- <vc-preamble>
def list_sum (xs : List Nat) : Nat :=
  xs.foldl (· + ·) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mem_alloc (banks : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mem_alloc_positive (banks : List Nat) (h : banks.length = 16) :
  mem_alloc banks > 0 :=
sorry

theorem mem_alloc_preserves_input (banks : List Nat) (h : banks.length = 16) :
  mem_alloc banks = mem_alloc banks :=
sorry

theorem mem_alloc_deterministic (banks : List Nat) (h : banks.length = 16) :
  mem_alloc banks = mem_alloc banks :=
sorry
-- </vc-theorems>