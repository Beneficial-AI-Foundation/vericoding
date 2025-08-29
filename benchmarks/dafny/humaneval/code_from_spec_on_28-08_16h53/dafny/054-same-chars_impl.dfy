// <vc-helpers>
predicate SameChars(s0: string, s1: string)
{
  multiset(s0) == multiset(s1)
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def same_chars(s0: string, s1: string) -> Bool
*/
// </vc-description>

// <vc-spec>
method same_chars(s0: string, s1: string) returns (result: bool)
  ensures result == SameChars(s0, s1)
// </vc-spec>
// <vc-code>
method same_chars(s0: string, s1: string) returns (result: bool)
  ensures result == SameChars(s0, s1)
{
  result := multiset(s0) == multiset(s1);
}
// </vc-code>
