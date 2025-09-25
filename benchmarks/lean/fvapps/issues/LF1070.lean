-- <vc-preamble>
def get_max_earnings (n l k : Nat) (groups : List (Nat × Nat × Nat × Nat)) : Nat :=
  sorry

def hash_state (groups : List Group) (i : Nat) : List Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def optimize (groups : List Group) : List Group :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_max_earnings_nonnegative (n l k : Nat) (groups : List (Nat × Nat × Nat × Nat)) :
  get_max_earnings n l k groups ≥ 0 :=
sorry

theorem get_max_earnings_bounded (n l k : Nat) (groups : List (Nat × Nat × Nat × Nat)) 
  (h : groups.length > 0) :
  get_max_earnings n l k groups ≤ groups.foldr (fun g acc => g.2.2.2 + acc) 0 :=
sorry 

theorem hash_state_length (groups : List Group) (i : Nat) :
  (hash_state groups i).length = groups.length + 1 :=
sorry

theorem hash_state_last_elem (groups : List Group) (i : Nat) 
  (h : hash_state groups i ≠ []) :
  (hash_state groups i).getLast h = i :=
sorry

theorem hash_state_ordered (groups : List Group) (i : Nat) (j : Nat) 
  (h : j + 1 < (hash_state groups i).length) :
  ((hash_state groups i)[j] ≤ (hash_state groups i)[j+1]) :=
sorry

theorem optimize_ordered (groups : List Group) (j : Nat)
  (h : j + 1 < (optimize groups).length) :
  ((optimize groups)[j]).start ≤ ((optimize groups)[j+1]).start :=
sorry

/-
info: 140
-/
-- #guard_msgs in
-- #eval get_max_earnings 5 5 4 [(2, 1, 5, 50), (1, 2, 4, 20), (2, 3, 4, 40), (2, 4, 5, 50), (3, 4, 5, 80)]

/-
info: 127200
-/
-- #guard_msgs in
-- #eval get_max_earnings 10 10 5 [(2, 5, 10, 17300), (2, 1, 8, 31300), (5, 4, 10, 27600), (4, 8, 10, 7000), (5, 9, 10, 95900), (2, 7, 10, 14000), (3, 6, 10, 63800), (1, 7, 10, 19300), (3, 8, 10, 21400), (2, 2, 10, 7000)]
-- </vc-theorems>