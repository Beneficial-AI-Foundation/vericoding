use vstd::prelude::*;

verus! {

spec fn sum_ints(n: int) -> int
    decreases n when n >= 0
{
    if n <= 0 {
        0
    } else {
        sum_ints(n - 1) + n
    }
}

// <vc-helpers>
proof fn sum_ints_formula(n: int)
    requires n >= 0
    ensures sum_ints(n) == n * (n + 1) / 2
    decreases n
{
    if n <= 0 {
        assert(sum_ints(n) == 0);
        assert(n * (n + 1) / 2 == 0);
    } else {
        sum_ints_formula(n - 1);
        assert(sum_ints(n - 1) == (n - 1) * n / 2);
        assert(sum_ints(n) == sum_ints(n - 1) + n);
        assert(sum_ints(n) == (n - 1) * n / 2 + n);
        assert(sum_ints(n) == (n - 1) * n / 2 + 2 * n / 2);
        assert(sum_ints(n) == ((n - 1) * n + 2 * n) / 2);
        assert(sum_ints(n) == (n * n - n + 2 * n) / 2);
        assert(sum_ints(n) == (n * n + n) / 2);
        assert(sum_ints(n) == n * (n + 1) / 2);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn sum_ints_loop(n: u32) -> (s: u32)
    ensures 
        s == sum_ints(n as int),
        s == n * (n + 1) / 2;
// </vc-spec>
// </vc-spec>

// <vc-code>
fn sum_ints_loop(n: u32) -> (s: u32)
    ensures 
        s == sum_ints(n as int),
        s == n * (n + 1) / 2
{
    let mut i: u32 = 0;
    let mut acc: u32 = 0;
    
    while i < n
        invariant 
            i <= n,
            acc == sum_ints(i as int)
    {
        i = i + 1;
        acc = acc + i;
    }
    
    proof {
        sum_ints_formula(n as int);
    }
    
    acc
}
// </vc-code>

fn main() {
}

}