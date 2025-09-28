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
// Helper lemma to show that gcd is symmetric
proof fn gcd_symmetric(x: int, y: int)
    requires x > 0 && y > 0
    ensures gcd(x, y) == gcd(y, x)
    decreases x + y
{
    if x == y {
        // Base case: gcd(x, x) == x == gcd(x, x)
    } else if x > y {
        // gcd(x, y) == gcd(x - y, y)
        // We need to show this equals gcd(y, x)
        // Since x > y, we have gcd(y, x) == gcd(y, x - y) by definition
        // But we need to show gcd(x - y, y) == gcd(y, x - y)
        gcd_symmetric(x - y, y);
    } else {
        // x < y, so gcd(x, y) == gcd(x, y - x)
        // and gcd(y, x) == gcd(y - x, x)
        gcd_symmetric(x, y - x);
    }
}

// Helper lemma to prove that gcd is preserved when we subtract
proof fn gcd_subtract_preserves(x: int, y: int)
    requires x > 0, y > 0, x > y
    ensures gcd(x, y) == gcd(x - y, y)
    decreases x + y
{
    // This follows directly from the definition of gcd
}

proof fn gcd_subtract_preserves_y(x: int, y: int) 
    requires x > 0, y > 0, y > x
    ensures gcd(x, y) == gcd(x, y - x)
    decreases x + y
{
    // This follows directly from the definition of gcd
}
// </vc-helpers>

// <vc-spec>
fn gcd_i(m: int, n: int) -> (d: int)
    requires m > 0 && n > 0
    ensures d == gcd(m, n)
// </vc-spec>
// <vc-code>
{
    let mut x: int = m;
    let mut y: int = n;
    
    while x != y
        invariant
            x > 0,
            y > 0,
            gcd(x, y) == gcd(m, n),
        decreases x + y,
    {
        if x > y {
            assert(gcd(x, y) == gcd(x - y, y));  // From gcd definition
            x = x - y;
        } else {
            assert(gcd(x, y) == gcd(x, y - x));  // From gcd definition
            y = y - x;
        }
    }
    
    assert(x == y);
    assert(gcd(x, y) == x);  // When x == y, gcd(x, x) == x by definition
    x
}
// </vc-code>

fn main() {
}

}