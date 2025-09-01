

// <vc-helpers>
// <vc-helpers>

// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method same_chars(s0 : string, s1 : string) returns (b : bool)
    // post-conditions-start
    ensures b == ((set i | i in s0) == (set i | i in s1))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  b := ((set i | i in s0) == (set i | i in s1));
}
// </vc-code>

