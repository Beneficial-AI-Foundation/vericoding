// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method square (n: int) returns (r: int)
    requires 0 <= n;
    ensures r == n*n;
// </vc-spec>
// <vc-code>
{
    var x: int;
    var i: int;

    r := 0;
    i := 0;
    x := 1;

    while (i < n)
        invariant i <= n;
        invariant r == i*i;
        invariant x == 2*i + 1;
    {
        r := r + x;
        x := x + 2;
        i := i + 1;
    }
}
// </vc-code>
