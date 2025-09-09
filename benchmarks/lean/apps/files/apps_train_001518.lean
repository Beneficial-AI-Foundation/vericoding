-- <vc-helpers>
-- </vc-helpers>

def find_max_height_visits (n : Nat) (heights : List Nat) : Nat :=
sorry

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

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_max_height_visits 5 [2, 2, 1, 2, 4]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_max_height_visits n2 heights2

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_max_height_visits n3 heights3

-- Apps difficulty: interview
-- Assurance level: unguarded