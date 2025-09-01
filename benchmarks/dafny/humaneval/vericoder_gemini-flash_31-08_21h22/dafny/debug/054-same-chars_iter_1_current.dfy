

// <vc-helpers>
function charSet(s: string): set<char>
  reads s
{
  if s == "" then
    {}
  else
    {s[0]} + charSet(s[1..])
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

