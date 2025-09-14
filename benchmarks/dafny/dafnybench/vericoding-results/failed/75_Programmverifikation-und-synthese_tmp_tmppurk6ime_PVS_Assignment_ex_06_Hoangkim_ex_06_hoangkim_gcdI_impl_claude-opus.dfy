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
    decreases if x > y then x else y
{
    if x == y {
        // gcd(x, x) == x == gcd(x, x)
    } else if x > y {
        // gcd(x, y) == gcd(x - y, y)
        // Need to show this equals gcd(y, x)
        // Since y < x, gcd(y, x) == gcd(y, x - y)
        gcdSymmetric(x - y, y);
    } else {
        // x < y
        // gcd(x, y) == gcd(x, y - x)
        // gcd(y, x) == gcd(y - x, x) since y > x
        gcdSymmetric(x, y - x);
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
    var x := m;
    var y := n;
    
    while x != y
        invariant x > 0 && y > 0
        invariant gcd(x, y) == gcd(m, n)
        decreases if x > y then x else y
    {
        if x > y {
            x := x - y;
        } else {
            y := y - x;
        }
    }
    
    d := x;
}
// </vc-code>

