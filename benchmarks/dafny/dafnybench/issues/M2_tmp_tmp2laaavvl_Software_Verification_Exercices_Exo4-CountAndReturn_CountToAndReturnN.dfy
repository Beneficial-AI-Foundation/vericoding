// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method CountToAndReturnN(n: int) returns (r: int)
    requires n >= 0
    ensures r == n
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < n
    invariant 0 <= i <= n
    {
        i := i + 1;
    }
    r := i;
}
// </vc-code>
