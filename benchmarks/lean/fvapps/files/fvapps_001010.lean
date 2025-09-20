-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_stone_value (N : Nat) (stones : List Int) : Int × Nat × Nat := sorry

theorem valid_indices {N : Nat} {stones : List Int} (h : N > 0) (h2 : stones.length > 0) : 
  let (val, start, finish) := find_max_stone_value N stones;
  0 ≤ start ∧ start ≤ finish ∧ finish < N := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem value_matches_slice {N : Nat} {stones : List Int} (h : N > 0) (h2 : stones.length > 0) :
  let (val, start, finish) := find_max_stone_value N stones;
  val = (List.range (finish - start + 1)).foldl (fun acc i => acc * stones[start + i]!) 1 := sorry 

theorem value_is_maximum {stones : List Int} (h : stones.length > 0) :
  let (val, start, finish) := find_max_stone_value (stones.length) stones;
  ∀ i j, 0 ≤ i → i ≤ j → j < stones.length → 
    val ≥ (List.range (j - i + 1)).foldl (fun acc k => acc * stones[i + k]!) 1 := sorry
-- </vc-theorems>