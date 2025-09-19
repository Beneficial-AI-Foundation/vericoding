-- <vc-preamble>
def mem_alloc (banks : List Nat) : Nat := sorry

theorem mem_alloc_positive (banks : List Nat) (h : banks.length = 16) :
  mem_alloc banks > 0 := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_sum (xs : List Nat) : Nat :=
  xs.foldl (· + ·) 0
-- </vc-definitions>

-- <vc-theorems>
theorem mem_alloc_preserves_input (banks : List Nat) (h : banks.length = 16) :
  mem_alloc banks = mem_alloc banks := sorry

theorem mem_alloc_deterministic (banks : List Nat) (h : banks.length = 16) :
  mem_alloc banks = mem_alloc banks := sorry
-- </vc-theorems>