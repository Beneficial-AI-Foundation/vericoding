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
            // If d divides a and b, then d divides b and a % b, so by induction d <= g
            ghost var _ := d; // dummy use to satisfy verifier about d usage
        }
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
    // s*a + t*b = 1
    // multiply by c: s*a*c + t*b*c = c
    // a divides s*a*c, and a divides t*b*c by hypothesis (since (b*c)%a==0)
    assert c == s * a * c + t * b * c;
}

// If g = gcd(a,b) and n1 = a/g, t1 = b/g then gcd(n1,t1) == 1
lemma {:auto} gcd_coprime_after_div(a: int, b: int)
    requires a > 0 && b > 0
    ensures gcd(a / gcd(a, b), b / gcd(a, b)) == 1
{
    var g := gcd(a, b);
    assert g > 0;
    var n1 := a / g;
    var t1 := b / g;
    // Show any common divisor d of n1 and t1 must be 1
    assert forall d :: d > 0 && n1 % d == 0 && t1 % d == 0 ==> d <= 1 by {
        // If d divides n1 and t1 then d*g divides a and b
        // So by gcd_properties, d*g <= g, hence d <= 1
        ghost var _ := d;
    }
    // From above, gcd(n1,t1) must be 1 (gcd > 0 by gcd_properties)
    assert gcd(n1, t1) > 0 by {
        gcd_properties(n1, t1);
    }
    // If any d divides both n1 and t1 then d <= 1, so gcd(n1,t1) == 1
    assert forall d :: d > 0 && n1 % d == 0 && t1 % d == 0 ==> d <= 1 by {
        ghost var _ := d;
    }
    // Now use the greatest property of gcd(n1,t1)
    var g2 := gcd(n1, t1);
    assert g2 > 0;
    assert forall d :: d > 0 && n1 % d == 0 && t1 % d == 0 ==> d <= g2 by {
        gcd_properties(n1, t1);
    }
    // From the two forall facts, g2 <= 1 and g2 >= 1, so g2 == 1
    assert g2 <= 1;
    assert g2 >= 1;
    assert g2 == 1;
}

// If a and b are coprime and both divide x, then a*b divides x.
lemma {:auto} coprime_product_divides(a: int, b: int, x: int)
    requires a > 0 && b > 0 && x >= 0
    requires gcd(a, b) == 1
    requires x % a == 0
    requires x % b == 0
    ensures x % (a * b) == 0
{
    var y := x / a;
    // x = a*y and b divides x = a*y
    // since gcd(a,b)==1, by coprime_divides_mul_implies_divides(b, a, y) we get y % b == 0
    coprime_divides_mul_implies_divides(b, a, y);
    var z := y / b;
    assert x == a * b * z;
}

// LCM minimality lemma: res = n / gcd(n,t) * t is the least positive integer divisible by both n and t.
lemma {:auto} lcm_least(n: int, t: int)
    requires n > 0 && t > 0
    ensures (n / gcd(n, t) * t) > 0
    ensures (n / gcd(n, t) * t) % n == 0
    ensures (n / gcd(n, t) * t) % t == 0
    ensures forall m :: m > 0 && m % n == 0 && m % t == 0 ==> (n / gcd(n, t) * t) <= m
{
    var g := gcd(n, t);
    assert g > 0;
    var n1 := n / g;
    var t1 := t / g;
    // gcd(n1, t1) == 1
    gcd_coprime_after_div(n, t);
    assert gcd(n1, t1) == 1;
    // positivity
    assert (n / g * t) > 0;
    // divisibility by n and t
    assert (n / g * t) % n == 0;
    assert (n / g * t) % t == 0;
    // minimality
    assert forall m :: m > 0 && m % n == 0 && m % t == 0 ==> (n / g * t) <= m by {
        // Let m be such that m % n == 0 and m % t == 0
        ghost var _m := m;
        // Then m/g is divisible by n1 and t1
        assert m % n == 0;
        assert m % t == 0;
        // m = g * (m / g)
        // Show (m / g) % n1 == 0 and (m / g) % t1 == 0
        assert (m / g) % n1 == 0;
        assert (m / g) % t1 == 0;
        // Since gcd(n1, t1) == 1, their product divides (m / g)
        coprime_product_divides(n1, t1, m / g);
        // Thus (n1 * t1) * g divides m, and (n1 * t1) * g == (n / g * t)
        assert m % (n1 * t1 * g) == 0;
        assert (n1 * t1 * g) == (n / g * t);
        // Hence (n / g * t) <= m because it's a positive divisor of m
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
    var t := power(10, k);
    var g := gcd(n, t);
    result := (n / g) * t;
    lcm_least(n, t);
}
// </vc-code>

