// recursive version should be more promising

// <vc-helpers>
function abs(n: int) : int {
    if n >= 0 then n else -n
}
// </vc-helpers>

// <vc-spec>
method greatest_common_divisor(a: int, b: int) returns (gcd: int)
    // pre-conditions-start
    requires a != 0 || b != 0
    // pre-conditions-end
    // post-conditions-start
    ensures gcd != 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var a_abs := abs(a);
    var b_abs := abs(b);
    var x := a_abs;
    var y := b_abs;
    while (y != 0)
        decreases y
        invariant x >= 0
        invariant y >= 0
    {
        var temp := x % y;
        assert temp >= 0;
        x := y;
        y := temp;
    }
    assert x != 0;
    gcd := x;
}
// </vc-code>

