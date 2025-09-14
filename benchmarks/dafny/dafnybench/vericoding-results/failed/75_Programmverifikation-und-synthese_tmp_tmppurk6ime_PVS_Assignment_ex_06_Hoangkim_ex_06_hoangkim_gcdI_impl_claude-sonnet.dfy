//Problem01
//a)
ghost function gcd(x: int, y: int): int
    requires x > 0 && y > 0
{
    if x == y then x
    else if x > y then gcd(x - y, y)
    else gcd(x, y - x)
}

//b)
ghost function gcd'(x: int, y: int): int
    requires x > 0 && y > 0
    decreases if x > y then x else y
{
    if x == y then x
    else if x > y then gcd'(x - y, y)
    else gcd(y, x)
}

// <vc-helpers>
lemma gcdSymmetric(x: int, y: int)
    requires x > 0 && y > 0
    ensures gcd(x, y) == gcd(y, x)
{
    if x == y {
        assert gcd(x, y) == x == y == gcd(y, x);
    } else if x > y {
        assert x - y > 0;
        gcdSymmetric(x - y, y);
        assert gcd(x, y) == gcd(x - y, y) == gcd(y, x - y) == gcd(y, x);
    } else {
        assert y - x > 0;
        gcdSymmetric(x, y - x);
        assert gcd(x, y) == gcd(x, y - x) == gcd(y - x, x) == gcd(y, x);
    }
}

lemma gcdModInvariant(x: int, y: int, k: int)
    requires x > 0 && y > 0 && k > 0 && x >= k * y
    ensures x - k * y > 0 ==> gcd(x, y) == gcd(x - k * y, y)
    ensures x - k * y == 0 ==> gcd(x, y) == y
    decreases k
{
    if k == 1 {
        assert x >= y;
        if x - y == 0 {
            assert x == y;
            assert gcd(x, y) == x == y;
        } else {
            assert x - y > 0;
            assert gcd(x, y) == gcd(x - y, y);
        }
    } else {
        assert k >= 2;
        assert x >= k * y >= 2 * y;
        assert x - (k - 1) * y >= y > 0;
        gcdModInvariant(x, y, k - 1);
        if x - k * y > 0 {
            assert x - k * y + y == x - (k - 1) * y;
            assert gcd(x - (k - 1) * y, y) == gcd(x - k * y, y);
        } else if x - k * y == 0 {
            if x - (k - 1) * y == y {
                assert gcd(x, y) == y;
            }
        }
    }
}

lemma gcdMod(x: int, y: int)
    requires x > 0 && y > 0
    ensures x % y > 0 ==> gcd(x, y) == gcd(x % y, y)
    ensures x % y == 0 ==> gcd(x, y) == y
{
    if x < y {
        assert x % y == x;
        assert gcd(x, y) == gcd(x % y, y);
    } else if x == y {
        assert x % y == 0;
        assert gcd(x, y) == x == y;
    } else {
        var q := x / y;
        var r := x % y;
        assert x == q * y + r;
        assert q > 0;
        if r == 0 {
            assert x == q * y;
            if q == 1 {
                assert x == y;
                assert gcd(x, y) == y;
            } else {
                gcdModInvariant(x, y, q);
                assert gcd(x, y) == y;
            }
        } else {
            assert r > 0;
            assert x - q * y == r > 0;
            gcdModInvariant(x, y, q);
            assert gcd(x, y) == gcd(r, y);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method gcdI(m: int, n: int) returns (d: int)
requires  m > 0 && n > 0 
ensures d == gcd(m, n);
// </vc-spec>
// <vc-code>
{
    var a := m;
    var b := n;
    
    while a != b
        invariant a > 0 && b > 0
        invariant gcd(a, b) == gcd(m, n)
        decreases a + b
    {
        if a > b {
            a := a - b;
        } else {
            b := b - a;
        }
    }
    
    d := a;
}
// </vc-code>

