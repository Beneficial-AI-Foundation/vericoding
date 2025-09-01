// recursive version should be more promising

// <vc-helpers>
function gcd_recursive(a: int, b: int): int
    requires a != 0 || b != 0
    decreases if a >= 0 then a else -a, if b >= 0 then b else -b
{
    if b == 0 then 
        if a >= 0 then a else -a
    else 
        gcd_recursive(b, a % b)
}

lemma gcd_recursive_nonzero(a: int, b: int)
    requires a != 0 || b != 0
    ensures gcd_recursive(a, b) != 0
{
    if b == 0 {
        assert gcd_recursive(a, b) == (if a >= 0 then a else -a);
        assert a != 0;
        assert (if a >= 0 then a else -a) > 0;
    } else {
        gcd_recursive_nonzero(b, a % b);
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
    gcd := gcd_recursive(a, b);
    gcd_recursive_nonzero(a, b);
}
// </vc-code>

