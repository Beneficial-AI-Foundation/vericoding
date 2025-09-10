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
lemma LCM_NonZero(a: int, b: int)
    requires a > 0 && b > 0
    ensures lcm(a, b) > 0
{
    var g := gcd(a, b);
    assert g > 0;
    assert a * b > 0;
    assert g != 0; // Prevents division by zero
    assert a * b / g > 0;
}

lemma LCM_Divides(a: int, b: int)
    requires a > 0 && b > 0
    ensures a % lcm(a, b) == 0 && b % lcm(a, b) == 0
{
    var g := gcd(a, b);
    var l := a * b / g;
    assert g != 0; // Prevents division by zero
    // Prove that a divides l
    assert a * b == g * l;
    assert l % a == 0 by {
        calc {
            l % a;
            (a * b / g) % a;
            { assert (a * b) % (g * a) == 0; }
            0;
        }
    }
    // Prove that b divides l
    assert l % b == 0 by {
        calc {
            l % b;
            (a * b / g) % b;
            { assert (a * b) % (g * b) == 0; }
            0;
        }
    }
    assert a % l == 0 && b % l == 0;
}

lemma LCM_IsMultiple(a: int, b: int)
    requires a > 0 && b > 0
    ensures forall m :: m > 0 && m % a == 0 && m % b == 0 ==> lcm(a, b) <= m
{
    var g := gcd(a, b);
    assert g != 0; // Prevents division by zero
    forall m | m > 0 && m % a == 0 && m % b == 0
        ensures lcm(a, b) <= m
    {
        assert m % g == 0;
        var a' := a / g;
        var b' := b / g;
        assert gcd(a', b') == 1;
        assert m % a' == 0;
        assert m % g == 0;
        assert m % (g * a') == 0;
        assert m % a == 0;
        // m must be at least g * a' * b' = a * b / g
        assert m >= a * b / g;
    }
}

lemma Power10_Positive(k: int)
    requires k >= 0
    ensures power(10, k) > 0
{
    if k > 0 {
        Power10_Positive(k - 1);
    }
}

function lcm(a: int, b: int): int
    requires a > 0 && b > 0
    ensures lcm(a, b) > 0
    ensures a % lcm(a, b) == 0 && b % lcm(a, b) == 0
    ensures forall m :: m > 0 && m % a == 0 && m % b == 0 ==> lcm(a, b) <= m
{
    var g := gcd(a, b);
    assert g > 0;
    assert g != 0; // Prevents division by zero
    a * b / g
}

function gcd(a: int, b: int): int
    requires a > 0 && b > 0
    ensures gcd(a, b) > 0
    decreases a, b
{
    if a == b then
        a
    else if a > b then
        gcd(a - b, b)
    else
        gcd(a, b - a)
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
    var p10 := power(10, k);
    Power10_Positive(k);
    assert p10 > 0;
    var l := lcm(n, p10);
    LCM_NonZero(n, p10);
    LCM_Divides(n, p10);
    LCM_IsMultiple(n, p10);
    assert l > 0;
    assert n % l == 0;
    assert p10 % l == 0;
    assert forall m :: m > 0 && m % n == 0 && m % p10 == 0 ==> l <= m;
    result := l;
}
// </vc-code>

