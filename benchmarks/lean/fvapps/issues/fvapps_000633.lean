-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def compare_strings (s1 s2 : String) : ComparisonResult := sorry

theorem compare_strings_reflexive (s : String) :
  s.length > 0 → compare_strings s s = ComparisonResult.equal := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem compare_strings_inverse (s1 s2 : String) :
  s1.length > 0 → s2.length > 0 →
  match compare_strings s1 s2 with
  | ComparisonResult.first => compare_strings s2 s1 = ComparisonResult.second
  | ComparisonResult.second => compare_strings s2 s1 = ComparisonResult.first
  | ComparisonResult.equal => compare_strings s2 s1 = ComparisonResult.equal
  := sorry

theorem compare_strings_ascii_order (s1 s2 : String) :
  s1.length > 0 → s2.length > 0 →
  (if s1.take (min s1.length s2.length) < s2.take (min s1.length s2.length) then
    compare_strings (s1.take (min s1.length s2.length)) (s2.take (min s1.length s2.length)) = ComparisonResult.first
  else if s1.take (min s1.length s2.length) > s2.take (min s1.length s2.length) then  
    compare_strings (s1.take (min s1.length s2.length)) (s2.take (min s1.length s2.length)) = ComparisonResult.second
  else
    compare_strings (s1.take (min s1.length s2.length)) (s2.take (min s1.length s2.length)) = ComparisonResult.equal)
  := sorry
-- </vc-theorems>