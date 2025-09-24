-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_height_visits (n : Nat) (heights : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_max_height_visits_bounds {n : Nat} {heights : List Nat} 
  (h1 : heights.length = n) (h2 : n > 0) :
  let result := find_max_height_visits n heights
  1 ≤ result ∧ result ≤ n :=
sorry

theorem find_max_height_visits_max_frequency {n : Nat} {heights : List Nat} 
  (h : heights.length = n) :
  find_max_height_visits n heights = 
    List.foldl (fun acc x => max acc (List.count x heights)) 0 heights :=
sorry

theorem find_max_height_visits_identical {n : Nat} {heights : List Nat} {h : Nat}
  (h1 : heights.length = n)
  (h2 : ∀ x ∈ heights, x = h) :
  find_max_height_visits n heights = n :=
sorry

theorem find_max_height_visits_order_invariant {n : Nat} {heights : List Nat}
  (h : heights.length = n) :
  find_max_height_visits n heights = find_max_height_visits n (List.reverse heights) :=
sorry

theorem find_max_height_visits_monotone {n : Nat} {heights : List Nat}
  (h : heights.length = n) :
  let result := find_max_height_visits n heights
  let max_freq_height := List.foldl 
    (fun acc x => if List.count x heights > List.count acc heights then x else acc) 
    (List.head! heights) 
    heights
  find_max_height_visits (n + 1) (heights ++ [max_freq_height]) ≥ result :=
sorry
-- </vc-theorems>