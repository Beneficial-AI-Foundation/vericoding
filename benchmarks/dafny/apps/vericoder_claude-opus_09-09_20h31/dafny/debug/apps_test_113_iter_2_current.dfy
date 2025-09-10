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
    ensures forall d :: d > 0 && a % d == 0 && b % d == 0 ==> d <= gcd(a, b)
    decreases b
{
    if b == 0 then a
    else gcd(b, a % b)
}

function lcm(a: int, b: int): int
    requires a > 0 && b > 0
    ensures lcm(a, b) > 0
    ensures lcm(a, b) % a == 0 && lcm(a, b) % b == 0
    ensures forall m :: m > 0 && m % a == 0 && m % b == 0 ==> lcm(a, b) <= m
{
    a * b / gcd(a, b)
}

lemma GcdProperties(a: int, b: int)
    requires a > 0 && b > 0
    ensures gcd(a, b) > 0
    ensures a % gcd(a, b) == 0 && b % gcd(a, b) == 0
    ensures gcd(a, b) <= a && gcd(a, b) <= b
{
    // The proof is by induction on b
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
    LcmProperties(n, p);
}
// </vc-code>

