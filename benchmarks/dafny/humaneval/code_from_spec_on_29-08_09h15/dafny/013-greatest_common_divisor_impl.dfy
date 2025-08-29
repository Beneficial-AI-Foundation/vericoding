// recursive version should be more promising

// <vc-helpers>
function gcd_func(a: int, b: int): int
    requires a != 0 || b != 0
    decreases if b >= 0 then b else -b
{
    if b == 0 then a
    else gcd_func(b, a % b)
}

lemma gcd_nonzero(a: int, b: int)
    requires a != 0 || b != 0
    ensures gcd_func(a, b) != 0
    decreases if b >= 0 then b else -b
{
    if b == 0 {
        assert gcd_func(a, b) == a;
        assert a != 0;
    } else {
        gcd_nonzero(b, a % b);
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def greatest_common_divisor(a: int, b: int) -> int
Return a greatest common divisor of two integers a and b
*/
// </vc-description>

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
    gcd := gcd_func(a, b);
    gcd_nonzero(a, b);
}
// </vc-code>

