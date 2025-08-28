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
proof fn gcd_decreases(x: int, y: int)
    requires x > 0 && y > 0
    ensures gcd(x, y) > 0
    decreases x + y
{
    if x == y {
    } else if x > y {
        gcd_decreases(x - y, y);
    } else {
        gcd_decreases(x, y - x);
    }
}

proof fn gcd_prime_eq_gcd(x: int, y: int)
    requires x > 0 && y > 0
    ensures gcd_prime(x, y) == gcd(x, y)
    decreases if x > y { x } else { y }, x + y
{
    if x == y {
    } else if x > y {
        gcd_prime_eq_gcd(x - y, y);
    } else {
        gcd_prime_eq_gcd(y, x);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn gcd_i(m: int, n: int) -> (d: int)
    requires m > 0 && n > 0
    ensures d == gcd(m, n)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn gcd_i(m: int, n: int) -> (d: int)
    requires m > 0 && n > 0
    ensures d == gcd(m, n)
    decreases m + n
{
    if m == n {
        m
    } else if m > n {
        gcd_i(m - n, n)
    } else {
        gcd_i(m, n - m)
    }
}
// </vc-code>

fn main() {
}

}