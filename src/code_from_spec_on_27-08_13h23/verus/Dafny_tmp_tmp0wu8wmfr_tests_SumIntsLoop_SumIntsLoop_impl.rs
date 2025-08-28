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
proof fn sum_ints_loop_invariant(n: int, i: int, s: int)
    requires
        0 <= i <= n,
        s == sum_ints(i),
    ensures
        s == i * (i + 1) / 2,
    decreases n - i
{
    if i == 0 {
        assert(sum_ints(0) == 0);
        assert(0 * (0 + 1) / 2 == 0);
    } else {
        sum_ints_loop_invariant(n, i - 1, sum_ints(i - 1));
        assert(sum_ints(i) == sum_ints(i - 1) + i);
        assert((i - 1) * i / 2 + i == i * (i + 1) / 2);
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
fn sum_ints_loop_impl(n: u32) -> (s: u32)
    ensures
        s == sum_ints(n as int),
        s == n * (n + 1) / 2
{
    let mut i: u32 = 0;
    let mut s: u32 = 0;
    while i < n
        invariant
            i <= n,
            s == sum_ints(i as int)
    {
        s = s + (i + 1);
        i = i + 1;
    }
    proof {
        sum_ints_loop_invariant(n as int, i as int, s as int);
    }
    s
}
// </vc-code>

fn main() {
}

}