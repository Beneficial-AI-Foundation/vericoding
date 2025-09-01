

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method truncate(x : real) returns (i : real)
    // pre-conditions-start
    requires x >= 0.0
    // pre-conditions-end
    // post-conditions-start
    ensures (0.0 <= x - i < 1.0)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var intPart: int := 0;
    while (intPart + 1) <= x
        invariant 0 <= intPart <= x
        variant x - intPart
    {
        intPart := intPart + 1;
    }
    i := intPart.ToReal();
}
// </vc-code>

