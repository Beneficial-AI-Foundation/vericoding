-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findShortestPrefix (n : Nat) (arr : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_shortest_prefix_bounds {n : Nat} {arr : List Int}
  (h : arr.length = n) (h1 : n > 0) :
  let result := findShortestPrefix n arr
  0 ≤ result ∧ result < n :=
sorry

theorem find_shortest_prefix_sorted_asc {n : Nat} {arr : List Int}
  (h : arr.length = n) (h1 : n > 0)
  (h2 : ∀ i j, i < j → j < arr.length → arr[i]! ≤ arr[j]!) :
  findShortestPrefix n arr = 0 :=
sorry

theorem find_shortest_prefix_single {arr : List Int}
  (h : arr.length = 1) :
  findShortestPrefix 1 arr = 0 :=
sorry

theorem find_shortest_prefix_constant {n : Nat} {arr : List Int}
  (h : arr.length = n) (h1 : n > 0)
  (h2 : ∀ i j, i < arr.length → j < arr.length → arr[i]! = arr[j]!) :
  findShortestPrefix n arr = 0 :=
sorry
-- </vc-theorems>