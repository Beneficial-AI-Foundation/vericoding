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
  var s0_chars := set i | i in s0;
  var s1_chars := set i | i in s1;
  b := s0_chars == s1_chars;
}
// </vc-code>
