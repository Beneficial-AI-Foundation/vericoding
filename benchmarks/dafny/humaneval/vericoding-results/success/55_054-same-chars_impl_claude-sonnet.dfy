// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method same_chars(s0 : string, s1 : string) returns (b : bool)

    ensures b == ((set i | i in s0) == (set i | i in s1))
// </vc-spec>
// <vc-code>
{
  var set0 := set i | i in s0;
  var set1 := set i | i in s1;
  b := set0 == set1;
}
// </vc-code>
