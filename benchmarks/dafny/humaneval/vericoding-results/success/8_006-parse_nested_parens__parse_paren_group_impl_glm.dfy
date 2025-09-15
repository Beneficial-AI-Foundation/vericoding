// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method parse_paren_group(s : string) returns (max_depth : int)

    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')'

    ensures max_depth >= 0
// </vc-spec>
// <vc-code>
{
    var current := 0;
    max_depth := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant current >= 0
        invariant max_depth >= 0
    {
        if s[i] == '(' {
            current := current + 1;
            if current > max_depth {
                max_depth := current;
            }
        } else {
            if current > 0 {
                current := current - 1;
            }
        }
        i := i + 1;
    }
}
// </vc-code>
