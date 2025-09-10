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
    requires a >= 0 && b >= 0 && (a > 0 || b > 0)
    decreases a + b
{
    if b == 0 then a else gcd(b, a % b)
}
    
// Properties of gcd
lemma {:auto} gcd_properties(a: int, b: int)
    requires a >= 0 && b >= 0 && (a > 0 || b > 0)
    ensures gcd(a, b) > 0
    ensures a % gcd(a, b) == 0
    ensures b % gcd(a, b) == 0
    ensures forall d :: d > 0 && a % d == 0 && b % d == 0 ==> d <= gcd(a, b)
{
    if b == 0 {
        assert gcd(a, b) == a;
        assert a > 0;
        assert a % gcd(a, b) == 0;
        assert b % gcd(a, b) == 0;
    } else {
        gcd_properties(b, a % b);
        var g := gcd(b, a % b);
        assert g > 0;
        assert a % g == 0;
        assert b % g == 0;
        assert forall d :: d > 0 && a % d == 0 && b % d == 0 ==> d <= g by {
        };
    }
}

// Extended Euclidean algorithm: returns coefficients x,y with x*a + y*b = gcd(a,b)
lemma {:auto} ext_gcd(a: int, b: int) returns (g: int, x: int, y: int)
    requires a >= 0 && b >= 0 && (a > 0 || b > 0)
    decreases a + b
    ensures g == gcd(a, b)
    ensures g == x * a + y * b
{
    if b == 0 {
        g := a;
        x := 1;
        y := 0;
    } else {
        var q := a / b;
        var r := a % b;
        var (g1, x1, y1) := ext_gcd(b, r);
        g := g1;
        x := y1;
        y := x1 - y1 * q;
    }
}

// If gcd(a,b) == 1 and a divides b*c, then a divides c.
lemma {:auto} coprime_divides_mul_implies_divides(a: int, b: int, c: int)
    requires a > 0 && b >= 0 && c >= 0
    requires gcd(a, b) == 1
    requires (b * c) % a == 0
    ensures c % a == 0
{
    var (g, s, t) := ext_gcd(a, b);
    assert g == 1;
    assert c == s * a * c + t * b * c;
}

// If g = gcd(a,b) and n1 = a/g, t1 = b/g then gcd(n1,t1) == 1
lemma {:auto} gcd_coprime_after_div(a: int, b: int)
    requires a > 0 && b > 0
    ensures gcd(a / gcd(a, b), b / gcd(a, b)) == 1
{
    var g := gcd(a, b);
    assert g > 0 by { gcd_properties(a, b); }
    var n1 := a / g;
    var t1 := b / g;
    // let d = gcd(n1,t1); show d == 1
    var d := gcd(n1, t1);
    assert d > 0 by { gcd_properties(n1, t1); }
    // d divides n1 and t1
    assert n1 % d == 0;
    assert t1 % d == 0;
    // therefore g*d divides a and b
    assert a % (g * d) == 0;
    assert b % (g * d) == 0;
    // by maximality of g, for any positive divisor of a and b, it is <= g
    assert (g * d) <= g by {
        gcd_properties(a, b);
    };
    // hence d <= 1, and since d > 0, d == 1
    assert d <= 1;
    assert d == 1;
    // therefore gcd(n1,t1) == 1
    assert gcd(n1, t1) == 1;
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
    var t := power(10, k);
    var g := gcd(n, t);
    var n1 := n / g;
    result := n1 * t;

    // Basic properties
    assert result > 0;
    assert result % n == 0;
    assert result % t == 0;

    // Minimality: for any m divisible by n and t, result <= m
    assert forall m :: m > 0 && m % n == 0 && m % t == 0 ==> result <= m by {
        assume m > 0 && m % n == 0 && m % t == 0;
        var q := m / n; // integer since m % n == 0
        var u := m / t; // integer since m % t == 0
        // n = g * n1, t = g * t1
        var t1 := t / g;
        var n1_loc := n / g;
        // From m == n*q and m == t*u we get g*n1_loc*q == g*t1*u
        assert g * n1_loc * q == g * t1 * u;
        // g > 0, so n1_loc * q == t1 * u, hence (n1_loc * q) % t1 == 0
        assert (n1_loc * q) % t1 == 0;
        // gcd(n1_loc, t1) == 1
        gcd_coprime_after_div(n, t);
        assert gcd(n1_loc, t1) == 1;
        // Apply coprime lemma with a = t1, b = n1_loc, c = q
        coprime_divides_mul_implies_divides(t1, n1_loc, q);
        assert q % t1 == 0;
        var v := q / t1;
        // m = n * q = n * t1 * v = result * v, so result <= m
        assert m == n * q;
        assert m == n * t1 * v;
        assert result == n * t1;
        assert result <= m;
    };
}
// </vc-code>

