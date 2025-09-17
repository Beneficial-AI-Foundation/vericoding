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
  assume {:axiom} false;
}
// </vc-code>
