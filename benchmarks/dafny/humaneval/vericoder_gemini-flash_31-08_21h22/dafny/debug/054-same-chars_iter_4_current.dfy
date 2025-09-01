

// <vc-helpers>
function charSet(s: string): set<char>
{
  var result: set<char> := {};
  for i := 0 to |s| - 1
    ensures forall k :: 0 <= k < |s| && k < i ==> s[k] in result
    ensures forall k :: i <= k < |s| ==> !(s[k] in result)
  {
    result := result + {s[i]};
  }
  return result;
}
// </vc-helpers>

// <vc-spec>
method same_chars(s0 : string, s1 : string) returns (b : bool)
    // post-conditions-start
    ensures b == ((set i | i in s0) == (set i | i in s1))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var s0_set := charSet(s0);
  var s1_set := charSet(s1);
  return s0_set == s1_set;
}
// </vc-code>

