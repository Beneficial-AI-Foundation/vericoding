-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tail_swap (strings : List String) : List String := sorry

theorem tail_swap_length (strings : List String)
  (h1 : strings.length = 2) :
  (tail_swap strings).length = 2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tail_swap_preserves_string_type (strings : List String)
  (h1 : strings.length = 2)
  (h2 : ∀ s ∈ strings, s.contains ':') :
  ∀ s ∈ tail_swap strings, s.contains ':' := sorry

theorem tail_swap_preserves_heads (strings : List String)
  (h1 : strings.length = 2)
  (h2 : ∀ s ∈ strings, s.contains ':')
  (h3 : 0 < (tail_swap strings).length)
  (h4 : 1 < (tail_swap strings).length)
  (h5 : 0 < strings.length)
  (h6 : 1 < strings.length) :
  ((tail_swap strings).get! 0).splitOn ":" = (strings.get! 0).splitOn ":" ∧ 
  ((tail_swap strings).get! 1).splitOn ":" = (strings.get! 1).splitOn ":" := sorry

theorem tail_swap_swaps_tails (strings : List String)
  (h1 : strings.length = 2)
  (h2 : ∀ s ∈ strings, s.contains ':')
  (h3 : 0 < (tail_swap strings).length)
  (h4 : 1 < (tail_swap strings).length)
  (h5 : 0 < strings.length)
  (h6 : 1 < strings.length) :
  List.get! (((tail_swap strings).get! 0).splitOn ":") 1 = List.get! ((strings.get! 1).splitOn ":") 1 ∧
  List.get! (((tail_swap strings).get! 1).splitOn ":") 1 = List.get! ((strings.get! 0).splitOn ":") 1 := sorry

theorem tail_swap_involution (s1 s2 : String)
  (h1 : s1.contains ':')
  (h2 : s2.contains ':') :
  tail_swap (tail_swap [s1, s2]) = [s1, s2] := sorry
-- </vc-theorems>