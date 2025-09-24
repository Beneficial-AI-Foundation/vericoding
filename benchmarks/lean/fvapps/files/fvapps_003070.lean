-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def the_biggest_search_keys : List String → String := sorry

theorem returns_string {keys : List String} :
  ∃ s : String, the_biggest_search_keys keys = s := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_input_returns_empty {keys : List String} :
  keys = [] → the_biggest_search_keys keys = "''" := sorry

theorem basic_properties {keys : List String} (h : keys ≠ []) :
  let result := the_biggest_search_keys keys
  let max_len := List.foldl (fun acc k => max acc k.length) 0 keys
  let result_list := (result.splitOn ",").map String.trim
  result ≠ "''" →
  (∀ k ∈ result_list, k.startsWith "'" ∧ k.endsWith "'") ∧
  result_list ≠ [] := sorry
-- </vc-theorems>