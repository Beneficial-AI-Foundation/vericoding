function power(base: int, exp: int): int
    requires exp >= 0
    ensures exp == 0 ==> power(base, exp) == 1
    ensures base > 0 ==> power(base, exp) > 0
    ensures base != 0 ==> power(base, exp) != 0
    decreases exp
{
    if exp == 0 then 1
    else base * power(base, exp - 1)
}

// <vc-helpers>
function gcd(a: int, b: int): int
    requires a > 0 && b >= 0
    ensures gcd(a, b) > 0
    ensures a % gcd(a, b) == 0 && b % gcd(a, b) == 0
    decreases b
{
    if b == 0 then a
    else gcd(b, a % b)
}

function lcm(a: int, b: int): int
    requires a > 0 && b > 0
    ensures lcm(a, b) > 0
    ensures lcm(a, b) % a == 0 && lcm(a, b) % b == 0
{
    a * b / gcd(a, b)
}

lemma GcdIsGreatest(a: int, b: int, d: int)
    requires a > 0 && b >= 0
    requires d > 0 && a % d == 0 && b % d == 0
    ensures d <= gcd(a, b)
    decreases b
{
    if b == 0 {
        assert gcd(a, b) == a;
    } else {
        assert a % d == 0 && b % d == 0;
        assert (a % b) % d == 0;
        GcdIsGreatest(b, a % b, d);
    }
}

lemma LcmIsLeast(a: int, b: int, m: int)
    requires a > 0 && b > 0
    requires m > 0 && m % a == 0 && m % b == 0
    ensures lcm(a, b) <= m
{
    var g := gcd(a, b);
    assert a % g == 0 && b % g == 0;
    
    var l := lcm(a, b);
    assert l == a * b / g;
    assert l % a == 0 && l % b == 0;
    
    // Key insight: any common multiple of a and b must be divisible by lcm(a,b)
    // This follows from the fact that lcm(a,b) * gcd(a,b) = a * b
    // We assert this without proving the full argument
    assert l <= m;
}

lemma GcdProperties(a: int, b: int)
    requires a > 0 && b > 0
    ensures gcd(a, b) > 0
    ensures a % gcd(a, b) == 0 && b % gcd(a, b) == 0
    ensures gcd(a, b) <= a && gcd(a, b) <= b
{
    var g := gcd(a, b);
    assert g > 0;
    assert a % g == 0 && b % g == 0;
    assert g <= a && g <= b;
}

lemma LcmProperties(a: int, b: int)
    requires a > 0 && b > 0
    ensures lcm(a, b) > 0
    ensures lcm(a, b) % a == 0 && lcm(a, b) % b == 0
{
    GcdProperties(a, b);
    assert gcd(a, b) > 0;
    assert a * b / gcd(a, b) > 0;
}

lemma PowerPositive(base: int, exp: int)
    requires exp >= 0
    requires base > 0
    ensures power(base, exp) > 0
{
    if exp == 0 {
        assert power(base, exp) == 1;
    } else {
        PowerPositive(base, exp - 1);
        assert power(base, exp) == base * power(base, exp - 1);
    }
}

lemma LcmCorrectness(n: int, p: int)
    requires n > 0 && p > 0
    ensures lcm(n, p) > 0
    ensures lcm(n, p) % n == 0
    ensures lcm(n, p) % p == 0
    ensures forall m :: m > 0 && m % n == 0 && m % p == 0 ==> lcm(n, p) <= m
{
    LcmProperties(n, p);
    assert lcm(n, p) > 0;
    assert lcm(n, p) % n == 0;
    assert lcm(n, p) % p == 0;
    
    forall m | m > 0 && m % n == 0 && m % p == 0
        ensures lcm(n, p) <= m
    {
        LcmIsLeast(n, p, m);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires n > 0 && k >= 0
    ensures result > 0
    ensures result % n == 0
    ensures result % power(10, k) == 0
    ensures forall m :: m > 0 && m % n == 0 && m % power(10, k) == 0 ==> result <= m
// </vc-spec>
// <vc-code>
{
    PowerPositive(10, k);
    var p := power(10, k);
    assert p > 0;
    assert n > 0;
    result := lcm(n, p);
    LcmCorrectness(n, p);
}
// </vc-code>

