use vstd::prelude::*;

verus! {

spec fn C(n: nat) -> nat
    decreases n
{
    if n == 0 { 
        1nat 
    } else { 
        ((4 * (n as int) - 2) * (C((n - 1) as nat) as int) / ((n as int) + 1)) as nat
    }
}

// <vc-helpers>
fn integer_sqrt(n: u64) -> (res: u64)
    ensures res * res <= n && (res + 1) * (res + 1) > n
{
    if n == 0 { return 0; }
    let mut x: u64 = n;
    let mut y: u64 = (x + 1) / 2;
    while y < x
        invariant x <= n
        invariant y <= n
        invariant y > 0
        invariant x > 0
        invariant x * x >= n // This should be x*x >= n / (Some_constant_here) or similar, but for positive integers it is fine
        invariant y * y <= n // This is the invariant that is good for the loop.
    {
        x = y;
        y = (x + n / x) / 2;
    }
    x
}
// </vc-helpers>

// <vc-spec>
fn calcC(n: u64) -> (res: u64)
    ensures res == C(n as nat),
// </vc-spec>
// <vc-code>
{
    let mut res: u64 = 1;
    let mut i: u64 = 1;
    while i <= n
        invariant res == C((i - 1) as nat) as u64
        decreases n - i
    {
        proof {
            assert(C(i as nat) == ((4 * (i as int) - 2) * (C((i - 1) as nat) as int) / ((i as int) + 1)) as nat);
        }
        res = res * (4 * i - 2) / (i + 1);
        i = i + 1;
    }
    res
}
// </vc-code>

fn main() {}

}