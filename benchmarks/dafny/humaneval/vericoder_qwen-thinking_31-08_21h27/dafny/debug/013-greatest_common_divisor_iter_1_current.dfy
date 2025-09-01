// recursive version should be more promising

// <vc-helpers>

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
    var a_abs := a.abs;
    var b_abs := b.abs;
    var x := a_abs;
    var y := b_abs;
    while (y != 0)
        decreases y
    {
        var temp := x % y;
        x := y;
        y := temp;
    }
    gcd := x;
}
// </vc-code>

