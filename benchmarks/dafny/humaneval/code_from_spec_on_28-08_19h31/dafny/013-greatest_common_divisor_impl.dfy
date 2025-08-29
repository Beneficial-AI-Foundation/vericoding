// recursive version should be more promising

// <vc-helpers>
function abs(x: int): int {
    if x < 0 then -x else x
}

lemma Divides(d: int, n: int)
    ensures d != 0 ==> (exists k: int :: n == k * d)
{
    if d != 0 {
        var k := n / d;
        assert n == k * d + n % d;
        if n % d == 0 {
            assert n == k * d;
        }
    }
}

lemma GCDProperties(a: int, b: int, gcd: int)
    requires a != 0 || b != 0
    requires gcd != 0
    requires exists k: int :: a == k * gcd
    requires exists m: int :: b == m * gcd
    ensures gcd != 0
    ensures exists k: int :: a == k * gcd
    ensures exists m: int :: b == m * gcd
{
}

lemma GCDInvariant(a: int, b: int, x: int, y: int, tempX: int, tempY: int)
    requires a != 0 || b != 0
    requires x == abs(a)
    requires y == abs(b)
    requires tempX != 0
    requires tempY >= 0
    requires exists k: int :: x == k * tempX
    requires exists m: int :: y == m * tempX
    ensures exists k: int :: x == k * tempX
    ensures exists m: int :: y == m * tempX
{
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
method ComputeGCD(a: int, b: int) returns (gcd: int)
    requires a != 0 || b != 0
    ensures gcd != 0
    ensures exists k: int :: a == k * gcd
    ensures exists m: int :: b == m * gcd
{
    var x := abs(a);
    var y := abs(b);
    
    if y == 0 {
        gcd := x;
        assert x != 0;
        if a != 0 {
            var k := if a < 0 then -1 else 1;
            assert a == k * x;
        } else {
            var m := if b < 0 then -1 else 1;
            assert b == m * x;
        }
        return x;
    }
    
    if x == 0 {
        gcd := y;
        assert y != 0;
        var m := if b < 0 then -1 else 1;
        assert b == m * y;
        return y;
    }
    
    var tempX := x;
    var tempY := y;
    while tempY != 0
        decreases tempY
        invariant tempX != 0
        invariant tempY >= 0
        invariant exists k: int :: x == k * tempX
        invariant exists m: int :: y == m * tempX
    {
        var temp := tempY;
        tempY := tempX % tempY;
        tempX := temp;
    }
    
    gcd := tempX;
    assert tempX != 0;
    var kx := if a == 0 then 0 else a / tempX;
    var ky := if b == 0 then 0 else b / tempX;
    assert a == kx * tempX;
    assert b == ky * tempX;
    return tempX;
}
// </vc-code>
