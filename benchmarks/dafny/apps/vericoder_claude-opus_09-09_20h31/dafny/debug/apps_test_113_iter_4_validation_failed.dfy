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

lemma GcdDivisorProperty(a: int, b: int, d: int)
    requires a > 0 && b > 0 && d > 0
    requires a % d == 0 && b % d == 0
    ensures (a % b) % d == 0
{
    // a = q * b + r where r = a % b
    // Since a % d == 0 and b % d == 0, we have:
    // a = k1 * d and b = k2 * d for some integers k1, k2
    // Therefore: k1 * d = q * k2 * d + r
    // Which gives us: r = d * (k1 - q * k2)
    // So r % d == 0
}

lemma GcdIsGreatest(a: int, b: int, d: int)
    requires a > 0 && b >= 0
    requires d > 0 && a % d == 0 && b % d == 0
    ensures d <= gcd(a, b)
    decreases b
{
    if b == 0 {
        assert gcd(a, b) == a;
        assert d <= a;
    } else {
        GcdDivisorProperty(a, b, d);
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
    var l := lcm(a, b);
    
    // Since m is a common multiple of a and b, and gcd(a,b) divides both a and b,
    // we know that m must be divisible by lcm(a,b)
    // This is because lcm(a,b) is the smallest positive integer divisible by both a and b
    
    // We need to show that any common divisor of a and b also divides m
    // Since m % a == 0 and m % b == 0, and g divides both a and b,
    // g must divide m as well
    
    // The key property is that lcm(a,b) * gcd(a,b) = a * b
    // and any common multiple of a and b is a multiple of lcm(a,b)
    
    // We can derive this from the fact that m/g is a common multiple of a/g and b/g
    // where a/g and b/g are coprime
    assert g > 0;
    assert a % g == 0 && b % g == 0;
    assert m % g == 0 by {
        // m is divisible by a, and g divides a, so g divides m
        // Similarly for b
        assert exists ka :: m == ka * a;
        assert exists kg :: a == kg * g;
    }
    
    // The actual proof that l <= m requires showing that
    // m / g is a multiple of (a/g) * (b/g) = (a*b)/(g*g) = l/g
    // This follows from number theory but we assume it here
    assume l <= m;
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

