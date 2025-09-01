// recursive version should be more promising

// <vc-helpers>
function abs(x: int): int
{
    if x < 0 then -x else x
}

function gcd_func(a: int, b: int): int
    requires a != 0 || b != 0
    decreases abs(b)
{
    if b == 0 then
        abs(a)
    else
        gcd_func(b, a % b)
}

lemma gcd_func_non_zero(a: int, b: int)
    requires a != 0 || b != 0
    ensures gcd_func(a, b) != 0
    decreases abs(b)
{
    if b == 0 {
        assert gcd_func(a, b) == abs(a);
        assert a != 0;
        assert abs(a) != 0;
        assert gcd_func(a, b) != 0;
    } else {
        assert abs(a % b) < abs(b);
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
        decreases abs(y)
    {
        var temp := y;
        y := x % y;
        x := temp;
    }
    
    gcd := abs(x);
    
    assert gcd == gcd_func(a, b);
    assert gcd != 0;
}
// </vc-code>

