-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reconstruct_queue (people : List (Nat × Nat)) : List (Nat × Nat) := sorry 

theorem reconstruct_queue_maintains_length 
  (people : List (Nat × Nat)) : 
  List.length (reconstruct_queue people) = List.length people := sorry

/- For any two heights in the input and output list, if we count their occurrences,
    they should be equal -/
-- </vc-definitions>

-- <vc-theorems>
theorem reconstruct_queue_maintains_elements
  (people : List (Nat × Nat)) (h : Nat) :
  List.countP (fun p => p.1 = h) (reconstruct_queue people) = 
  List.countP (fun p => p.1 = h) people := sorry

theorem reconstruct_queue_height_bounds
  (people : List (Nat × Nat)) :
  ∀ p ∈ people, 1 ≤ p.fst ∧ p.fst ≤ 100 := sorry

theorem reconstruct_queue_count_bounds
  (people : List (Nat × Nat)) :
  ∀ p ∈ people, 0 ≤ p.snd ∧ p.snd ≤ 20 := sorry

theorem reconstruct_queue_size_bounds
  (people : List (Nat × Nat)) :
  1 ≤ List.length people ∧ List.length people ≤ 20 := sorry
-- </vc-theorems>