// recursive version should be more promising
method greatest_common_divisor(a: int, b: int) returns (gcd: int)
    // pre-conditions-start
    requires a != 0 || b != 0
    // pre-conditions-end
    // post-conditions-start
    ensures gcd != 0
    // post-conditions-end
{
    // impl-start
    var x := a;
    var y := b;
    while (y != 0)
        // invariants-start
        invariant x != 0 || y != 0
        // invariants-end
    {
        var temp := y;
        y := x % y;
        x := temp;
    }
    gcd := x;
    // impl-end
}
