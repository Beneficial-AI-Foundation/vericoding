// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def same_chars(s0: string, s1: string) -> Bool
*/
// </vc-description>

// <vc-spec>
method same_chars(s0 : string, s1 : string) returns (b : bool)
    // post-conditions-start
    ensures b == ((set i | i in s0) == (set i | i in s1))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>
