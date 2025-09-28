use vstd::prelude::*;

verus! {

//Problem01
//a)
spec fn gcd(x: int, y: int) -> int
    recommends x > 0 && y > 0
    decreases x + y when x > 0 && y > 0
{
    if x == y { x }
    else if x > y { gcd(x - y, y) }
    else { gcd(x, y - x) }
}

//b)
spec fn gcd_prime(x: int, y: int) -> int
    recommends x > 0 && y > 0
    decreases if x > y { x } else { y }, x + y when x > 0 && y > 0
{
    if x == y { x }
    else if x > y { gcd_prime(x - y, y) }
    else { gcd(y, x) }
}

// <vc-helpers>
proof fn gcd_positive(x: int, y: int)
    requires x > 0 && y > 0
    ensures gcd(x, y) > 0
    decreases x + y
{
    if x == y {
    } else if x > y {
        gcd_positive(x - y, y);
    } else {
        gcd_positive(x, y - x);
    }
}

proof fn gcd_symmetric(x: int, y: int)
    requires x > 0 && y > 0
    ensures gcd(x, y) == gcd(y, x)
    decreases x + y
{
    if x == y {
    } else if x > y {
        gcd_symmetric(x - y, y);
        assert(gcd(x, y) == gcd(x - y, y));
        gcd_symmetric(y, x - y);
        assert(gcd(y, x - y) == gcd(x - y, y));
    } else {
        gcd_symmetric(x, y - x);
        assert(gcd(x, y) == gcd(x, y - x));
        gcd_symmetric(y - x, x);
        assert(gcd(y - x, x) == gcd(x, y - x));
    }
}

proof fn gcd_commutative(x: int, y: int)
    requires x > 0 && y > 0
    ensures gcd(x, y) == gcd(y, x)
{
    gcd_symmetric(x, y);
}

proof fn gcd_decreases(x: int, y: int)
    requires x > 0 && y > 0
    ensures x + y > 0 && (if x > y { (x - y) + y } else { x + (y - x) }) < x + y
{
}
// </vc-helpers>

// <vc-spec>
fn gcd_i(m: int, n: int) -> (d: int)
    requires m > 0 && n > 0
    ensures d == gcd(m, n)
// </vc-spec>
// <vc-code>
{
    let mut a = m;
    let mut b = n;
    
    proof {
        gcd_commutative(m, n);
    }
    
    while a != b
        invariant
            a > 0 && b > 0,
            gcd(a, b) == gcd(m, n),
        decreases a + b
    {
        if a > b {
            proof {
                gcd_decreases(a, b);
                assert(gcd(a, b) == gcd(a - b, b));
            }
            a = a - b;
        } else {
            proof {
                gcd_decreases(b, a);
                gcd_commutative(a, b);
                assert(gcd(a, b) == gcd(b, a));
                assert(gcd(b, a) == gcd(b - a, a));
                gcd_commutative(b - a, a);
                assert(gcd(b - a, a) == gcd(a, b - a));
            }
            b = b - a;
        }
    }
    
    proof {
        gcd_positive(m, n);
    }
    
    a
}
// </vc-code>

fn main() {
}

}