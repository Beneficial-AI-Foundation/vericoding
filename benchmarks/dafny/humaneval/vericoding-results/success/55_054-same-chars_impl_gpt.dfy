// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Chars(s: string): set<char> { set c | c in s }
// </vc-helpers>

// <vc-spec>
method same_chars(s0 : string, s1 : string) returns (b : bool)

    ensures b == ((set i | i in s0) == (set i | i in s1))
// </vc-spec>
// <vc-code>
{
  b := Chars(s0) == Chars(s1);
}
// </vc-code>
