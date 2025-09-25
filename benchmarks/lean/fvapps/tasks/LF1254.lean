-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_faster_batmobiles (n : Nat) (speeds : List Nat) : Nat := sorry

theorem count_faster_batmobiles_non_negative 
  (n : Nat) (speeds : List Nat) (h : speeds.length > 0) :
  count_faster_batmobiles n speeds ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_faster_batmobiles_bounded
  (n : Nat) (speeds : List Nat) (h : speeds.length > 0) :
  count_faster_batmobiles n speeds ≤ speeds.length - 1 := sorry 

theorem count_faster_batmobiles_matches_manual_count
  (n : Nat) (speeds : List Nat) (h : speeds.length > 0) :
  count_faster_batmobiles n speeds = 
    (List.filter (λ s => s > List.head! speeds) (List.tail! speeds)).length := sorry

theorem count_faster_batmobiles_single_slower
  (speeds : List Nat) (h : speeds = [2, 1]) :
  count_faster_batmobiles 1 speeds = 0 := sorry

theorem count_faster_batmobiles_single_faster  
  (speeds : List Nat) (h : speeds = [1, 2]) :
  count_faster_batmobiles 1 speeds = 1 := sorry
-- </vc-theorems>