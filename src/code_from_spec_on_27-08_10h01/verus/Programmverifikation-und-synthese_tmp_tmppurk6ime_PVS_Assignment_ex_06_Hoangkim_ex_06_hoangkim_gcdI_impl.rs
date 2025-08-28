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
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn gcd_i(m: int, n: int) -> (d: int)
    requires m > 0 && n > 0
    ensures d == gcd(m, n)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut x = m;
    let mut y = n;
    
    while x != y
        invariant x > 0 && y > 0
        invariant gcd(x, y) == gcd(m, n)
        decreases x + y
    {
        if x > y {
            x = x - y;
        } else {
            y = y - x;
        }
    }
    
    x
}
// </vc-code>

fn main() {
}

}