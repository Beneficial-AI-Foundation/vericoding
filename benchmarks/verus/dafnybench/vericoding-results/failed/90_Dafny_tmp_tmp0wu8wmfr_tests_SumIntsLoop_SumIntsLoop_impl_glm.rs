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

// </vc-helpers>

// <vc-spec>
fn sum_ints_loop(n: u32) -> (s: u32)
    ensures 
        s == sum_ints(n as int),
        s == n * (n + 1) / 2;
// </vc-spec>
// <vc-code>
{
    let mut s: u32 = 0;
    let mut i: u32 = 0;
    while i < n
        invariant 0 <= i <= n
        invariant s == sum_ints(i as int)
        invariant 2 * (s as u64) == (i as u64) * (i as u64 + 1)
        decreases n - i
    {
        i = i + 1;
        s = s + i;
    }
    s
}
// </vc-code>

fn main() {
}

}