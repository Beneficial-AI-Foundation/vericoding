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
fn gcd_i(m: int, n: int) -> (d: int)
    requires m > 0 && n > 0
    ensures d == gcd(m, n)
// </vc-spec>
// <vc-code>
{
    let mut a = m;
    let mut b = n;
    while a != b
        invariant
            a > 0 && b > 0 && gcd(a, b) == gcd(m, n)
        decreases a + b
    {
        if a > b {
            a = a - b;
        } else {
            b = b - a;
        }
    }
    a
}
// </vc-code>

fn main() {
}

}