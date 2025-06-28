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

fn gcdI(m: u32, n: u32) -> (d: u32)
    requires
        m > 0 && n > 0
    ensures
        d == gcd(m as int, n as int)
    decreases m + n
{
    if m == n {
        m
    } else if m < n {
        gcdI(m, n - m)
    } else {
        gcdI(m - n, n)
    }
}

// Proof function to establish the relationship between the iterative and recursive definitions
proof fn gcd_equivalence(m: u32, n: u32)
    requires m > 0 && n > 0
    ensures gcd(m as int, n as int) == gcd_iter(m as int, n as int)
    decreases m + n
{
    if m == n {
        // Base case: gcd(m, m) = m
    } else if m < n {
        // Prove gcd(m, n) == gcd(m, n-m)
        assert(gcd(m as int, n as int) == gcd(m as int, (n - m) as int));
        gcd_equivalence(m, n - m);
    } else {
        // Prove gcd(m, n) == gcd(m-n, n)  
        assert(gcd(m as int, n as int) == gcd((m - n) as int, n as int));
        gcd_equivalence(m - n, n);
    }
}

spec fn gcd_iter(m: int, n: int) -> int
    decreases m + n
{
    if m == n {
        m
    } else if m < n && m > 0 && n > 0 {
        gcd_iter(m, n - m)
    } else if m > n && m > 0 && n > 0 {
        gcd_iter(m - n, n)
    } else {
        gcd(m, n)
    }
}

}