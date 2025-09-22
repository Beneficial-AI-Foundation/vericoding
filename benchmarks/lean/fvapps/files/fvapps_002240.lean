-- <vc-preamble>
def list_sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | h :: t => h + list_sum t

def calculate_movable_sum (n d : Nat) (haybales : List Nat) : Nat :=
  let rec aux : Nat → Nat → Nat
    | 0, acc => acc
    | i+1, acc =>
      let moves := d / (i+1)
      let val := match haybales.get? i with
        | none => 0
        | some x => min moves x
      aux i (acc + val)
  aux (n-1) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_haystack (n : Nat) (d : Nat) (haybales : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_haystack_within_first_pile_sum {n d : Nat} {haybales : List Nat}
  (hn : n > 0) (h_len : haybales.length = n) :
  solve_haystack n d haybales ≥ (haybales.get ⟨0, sorry⟩) := by
  sorry

theorem solve_haystack_within_total_sum {n d : Nat} {haybales : List Nat}
  (hn : n > 0) (h_len : haybales.length = n) :
  solve_haystack n d haybales ≤ list_sum haybales := by
  sorry

theorem solve_haystack_within_movable_limit {n d : Nat} {haybales : List Nat}
  (hn : n > 0) (h_len : haybales.length = n) :
  solve_haystack n d haybales ≤
    (haybales.get ⟨0, sorry⟩) + calculate_movable_sum n d haybales := by
  sorry

theorem solve_haystack_single_pile {d : Nat} {hay : Nat} :
  solve_haystack 1 d [hay] = hay := by
  sorry

theorem solve_haystack_zero_days {n : Nat} {haybales : List Nat}
  (hn : n > 0) (h_len : haybales.length = n) :
  solve_haystack n 0 haybales = haybales.get ⟨0, sorry⟩ := by
  sorry
-- </vc-theorems>