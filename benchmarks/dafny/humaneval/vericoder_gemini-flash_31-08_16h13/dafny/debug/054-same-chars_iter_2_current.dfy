

// <vc-helpers>
function charSet(s: string): set<char>
  reads s `s` // `s` is a sequence, not an object. But a sequence is also a valid type for a reads clause.
  ensures charSet(s) == (set i | i in s)
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
  b := charSet(s0) == charSet(s1);
}
// </vc-code>

