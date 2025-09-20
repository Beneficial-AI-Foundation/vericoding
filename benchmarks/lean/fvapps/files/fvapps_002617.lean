-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def make_sequences (n : Nat) : Nat := sorry 

abbrev sum_list : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + sum_list xs
-- </vc-definitions>

-- <vc-theorems>
theorem count_at_least_one (n : Nat) (h: n > 0) : 
  make_sequences n ≥ 1 := sorry

theorem deterministic (n : Nat) (h: n > 0) :
  make_sequences n = make_sequences n := sorry

theorem monotonic_up_to_n (n : Nat) (h: n > 1) :
  make_sequences n ≥ make_sequences (n-1) := sorry

theorem recursive_relation (n : Nat) (h: n > 0) :
  make_sequences n = 1 + sum_list (List.map make_sequences (List.range (n/2))) := sorry
-- </vc-theorems>