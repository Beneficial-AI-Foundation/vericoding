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
        // gcd(a,0) == a
        assert gcd(a, b) == a;
        assert a > 0;
        // a divides a
        assert a % gcd(a, b) == 0;
        // 0 % a == 0
        assert b % gcd(a, b) == 0;
        // greatest: any d dividing a and 0 must be <= a
        // trivial since a is the value
    } else {
        // Use induction on (b, a % b)
        gcd_properties(b, a % b);
        // Let g = gcd(b, a % b) = gcd(a,b)
        // From induction we have:
        // g > 0, b % g == 0, (a % b) % g == 0, and g is greatest
        // Show a % g == 0:
        var g := gcd(b, a % b);
        assert g > 0;
        // a = (a / b) * b + (a % b)
        // since b % g == 0 and (a % b) % g == 0, a % g == 0
        assert a % g == 0;
        // b % g == 0 already holds
        assert b % g == 0;
        // greatest: if d divides a and b then d divides b and a % b,
        // hence by induction d <= g
        // Formalize:
        assert forall d :: d > 0 && a % d == 0 && b % d == 0 ==> d <= g by {
            // Given such d, since a % d == 0 and b % d == 0,
            // (a % b) % d == 0 as well. So d divides b and (a % b).
            // By induction's greatest property on (b, a % b), d <= g.
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
        // gcd(a,0) == a and 1*a + 0*0 == a
    } else {
        var q := a / b;
        var r := a % b;
        var (g1, x1, y1) := ext_gcd(b, r);
        g := g1;
        x := y1;
        y := x1 - y1 * q;
        // Verify combination:
        // x*a + y*b = y1*a + (x1 - y1*q)*b = y1*(q*b + r) + x1*b - y1*q*b = x1*b + y1*r = g1
        // And g1 == gcd(b, r) == gcd(a, b)
    }
}

// If gcd(a,b) == 1 and a divides b*c, then a divides c.
lemma {:auto} coprime_divides_mul_implies_divides(a: int, b: int, c: int)
    requires a > 0 && b >= 0 && c >= 0
    requires gcd(a, b) == 1
    requires (b * c) % a == 0
    ensures c % a == 0
{
    // Use extended gcd to get s,t with s*a + t*b = 1
    var (g, s, t) := ext_gcd(a, b);
    assert g == 1;
    // Multiply equation by c: s*a*c + t*b*c = c
    // a divides s*a*c and also divides t*b*c by hypothesis, so a divides c.
    assert c == s * a * c + t * b * c;
    // a divides left two terms, hence divides c
}

// If g = gcd(a,b) and n1 = a/g, t1 = b/g then gcd(n1,t1) == 1
lemma {:auto} gcd_coprime_after_div(a: int, b: int)
    requires a > 0 && b > 0
    ensures gcd(a / gcd(a, b), b / gcd(a, b)) == 1
{
    var g := gcd
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
        // gcd(a,0) == a
        assert gcd(a, b) == a;
        assert a > 0;
        // a divides a
        assert a % gcd(a, b) == 0;
        // 0 % a == 0
        assert b % gcd(a, b) == 0;
        // greatest: any d dividing a and 0 must be <= a
        // trivial since a is the value
    } else {
        // Use induction on (b, a % b)
        gcd_properties(b, a % b);
        // Let g = gcd(b, a % b) = gcd(a,b)
        // From induction we have:
        // g > 0, b % g == 0, (a % b) % g == 0, and g is greatest
        // Show a % g == 0:
        var g := gcd(b, a % b);
        assert g > 0;
        // a = (a / b) * b + (a % b)
        // since b % g == 0 and (a % b) % g == 0, a % g == 0
        assert a % g == 0;
        // b % g == 0 already holds
        assert b % g == 0;
        // greatest: if d divides a and b then d divides b and a % b,
        // hence by induction d <= g
        // Formalize:
        assert forall d :: d > 0 && a % d == 0 && b % d == 0 ==> d <= g by {
            // Given such d, since a % d == 0 and b % d == 0,
            // (a % b) % d == 0 as well. So d divides b and (a % b).
            // By induction's greatest property on (b, a % b), d <= g.
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
        // gcd(a,0) == a and 1*a + 0*0 == a
    } else {
        var q := a / b;
        var r := a % b;
        var (g1, x1, y1) := ext_gcd(b, r);
        g := g1;
        x := y1;
        y := x1 - y1 * q;
        // Verify combination:
        // x*a + y*b = y1*a + (x1 - y1*q)*b = y1*(q*b + r) + x1*b - y1*q*b = x1*b + y1*r = g1
        // And g1 == gcd(b, r) == gcd(a, b)
    }
}

// If gcd(a,b) == 1 and a divides b*c, then a divides c.
lemma {:auto} coprime_divides_mul_implies_divides(a: int, b: int, c: int)
    requires a > 0 && b >= 0 && c >= 0
    requires gcd(a, b) == 1
    requires (b * c) % a == 0
    ensures c % a == 0
{
    // Use extended gcd to get s,t with s*a + t*b = 1
    var (g, s, t) := ext_gcd(a, b);
    assert g == 1;
    // Multiply equation by c: s*a*c + t*b*c = c
    // a divides s*a*c and also divides t*b*c by hypothesis, so a divides c.
    assert c == s * a * c + t * b * c;
    // a divides left two terms, hence divides c
}

// If g = gcd(a,b) and n1 = a/g, t1 = b/g then gcd(n1,t1) == 1
lemma {:auto} gcd_coprime_after_div(a: int, b: int)
    requires a > 0 && b > 0
    ensures gcd(a / gcd(a, b), b / gcd(a, b)) == 1
{
    var g := gcd
// </vc-code>

