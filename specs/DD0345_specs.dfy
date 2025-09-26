// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Mult(x:nat, y:nat) returns (r: nat)
ensures r == x * y
// </vc-spec>
// <vc-code>
{
    var m := x;
    var n := y;
    r:=0;

    while m > 0
    invariant m >= 0
    invariant m*n+r == x*y
    {
        r := r + n;
        m := m - 1;
    }

    return r;
}
// </vc-code>
