use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn gcd(m: int, n: int) -> int
    decreases m, n
{
    if m == 0 {
        n
    } else if n == 0 {
        m
    } else if m <= n {
        gcd(m, n % m)
    } else {
        gcd(m % n, n)
    }
}

fn gcdI(m: int, n: int) -> (d: int)
    requires
        m > 0 && n > 0
    ensures
        d == gcd(m, n)
    decreases m, n
{
    if m == n {
        m
    } else if m < n {
        gcdI(m, n - m)
    } else {
        gcdI(m - n, n)
    }
}

}