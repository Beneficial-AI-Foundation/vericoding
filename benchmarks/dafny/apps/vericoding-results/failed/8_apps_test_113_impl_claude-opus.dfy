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

lemma GcdDivides(a: int, b: int)
    requires a > 0 && b >= 0
    ensures a % gcd(a, b) == 0 && b % gcd(a, b) == 0
{
    // Follows from function postcondition
}

lemma GcdIsGreatest(a: int, b: int, d: int)
    requires a > 0 && b >= 0
    requires d > 0 && a % d == 0 && b % d == 0
    ensures d <= gcd(a, b)
    decreases b
{
    if b == 0 {
        // gcd(a, 0) == a, and since a % d == 0, we have d <= a
    } else {
        // If d divides both a and b, then d divides a % b
        assert (a % b) % d == 0;
        GcdIsGreatest(b, a % b, d);
    }
}

lemma LcmDivides(a: int, b: int)
    requires a > 0 && b > 0
    ensures lcm(a, b) % a == 0 && lcm(a, b) % b == 0
{
    var g := gcd(a, b);
    var l := a * b / g;
    
    // Since g divides a, we have a = g * (a/g)
    // So l = a * b / g = (a/g) * b
    assert a % g == 0;
    assert l == (a / g) * b;
    assert l % a == 0;
    
    // Similarly for b
    assert b % g == 0;
    assert l == a * (b / g);
    assert l % b == 0;
}

lemma LcmIsLeast(a: int, b: int, m: int)
    requires a > 0 && b > 0
    requires m > 0 && m % a == 0 && m % b == 0
    ensures lcm(a, b) <= m
{
    var g := gcd(a, b);
    var l := a * b / g;
    
    // m is divisible by both a and b
    // So m is divisible by lcm(a, b)
    
    // Let's show that g divides m
    assert a % g == 0 && b % g == 0;
    
    // Since m % a == 0, we have m = k * a for some k
    // Since m % b == 0 and b % g == 0, we have m % g == 0
    
    // We know m/g is divisible by both a/g and b/g
    // And gcd(a/g, b/g) = 1
    
    // Therefore m/g is divisible by (a/g) * (b/g) = (a*b)/(g*g)
    // So m >= g * (a*b)/(g*g) = a*b/g = lcm(a,b)
    
    // Direct approach: use the fact that any common multiple must be >= lcm
    var ag := a / g;
    var bg := b / g;
    
    assert m % a == 0;
    assert exists k :: m == k * a;
    
    var k :| m == k * a;
    assert m == k * a;
    assert m % b == 0;
    assert (k * a) % b == 0;
    
    // k * a is divisible by b
    // a = ag * g and b = bg * g where gcd(ag, bg) = 1
    // So k * ag * g is divisible by bg * g
    // Therefore k * ag is divisible by bg
    
    // Since gcd(ag, bg) = 1, we have bg divides k
    assert k >= bg;
    assert m == k * a >= bg * a == bg * ag * g == (a * b) / g == l;
}

lemma PowerPositive(base: int, exp: int)
    requires exp >= 0
    requires base > 0
    ensures power(base, exp) > 0
{
    if exp == 0 {
        // power(base, 0) == 1 > 0
    } else {
        PowerPositive(base, exp - 1);
        // power(base, exp) == base * power(base, exp - 1) > 0
    }
}

lemma LcmCorrectness(n: int, p: int)
    requires n > 0 && p > 0
    ensures lcm(n, p) > 0
    ensures lcm(n, p) % n == 0
    ensures lcm(n, p) % p == 0
    ensures forall m :: m > 0 && m % n == 0 && m % p == 0 ==> lcm(n, p) <= m
{
    LcmDivides(n, p);
    
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
    result := lcm(n, p);
    LcmCorrectness(n, p);
}
// </vc-code>

