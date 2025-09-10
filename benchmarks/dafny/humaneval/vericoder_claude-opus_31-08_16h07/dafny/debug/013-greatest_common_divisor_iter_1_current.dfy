// recursive version should be more promising

// <vc-helpers>
function gcd_func(a: int, b: int): int
    requires a != 0 || b != 0
    decreases if a < 0 then -a else a, if b < 0 then -b else b
{
    if b == 0 then
        if a < 0 then -a else a
    else
        gcd_func(b, a % b)
}

lemma gcd_func_non_zero(a: int, b: int)
    requires a != 0 || b != 0
    ensures gcd_func(a, b) != 0
{
    if b == 0 {
        assert gcd_func(a, b) == (if a < 0 then -a else a);
        assert a != 0;
        assert gcd_func(a, b) != 0;
    } else {
        gcd_func_non_zero(b, a % b);
    }
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
    gcd_func_non_zero(a, b);
    var x := a;
    var y := b;
    
    while y != 0
        invariant x != 0 || y != 0
        invariant gcd_func(x, y) == gcd_func(a, b)
        decreases if y < 0 then -y else y
    {
        var temp := y;
        y := x % y;
        x := temp;
    }
    
    if x < 0 {
        gcd := -x;
    } else {
        gcd := x;
    }
    
    assert gcd == gcd_func(a, b);
    assert gcd != 0;
}
// </vc-code>

