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
proof fn sum_ints_succ(m: int)
    requires m >= 0
    ensures sum_ints(m + 1) == sum_ints(m) + (m + 1)
    decreases m
{
    if m == 0 {
        assert(sum_ints(1) == sum_ints(0) + 1);
    } else {
        assert(sum_ints(m + 1) == sum_ints((m + 1) - 1) + (m + 1));
        assert((m + 1) - 1 == m);
        assert(sum_ints((m + 1) - 1) == sum_ints(m));
        assert(sum_ints(m + 1) == sum_ints(m) + (m + 1));
    }
}

proof fn sum_ints_succ_u32(i: u32)
    ensures sum_ints((i as int) + 1) == sum_ints(i as int) + ((i as int) + 1)
{
    sum_ints_succ(i as int);
}

proof fn sum_ints_formula(m: int)
    requires m >= 0
    ensures sum_ints(m) == m * (m + 1) / 2
    decreases m
{
    if m == 0 {
        assert(sum_ints(0) == 0);
    } else {
        sum_ints_formula(m - 1);
        assert(sum_ints(m) == sum_ints(m - 1) + m);
        assert(sum_ints(m - 1) == (m - 1) * m / 2);
        assert(sum_ints(m) == (m - 1) * m / 2 + m);
        assert((m - 1) * m / 2 + m == m * (m + 1) / 2);
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_ints_loop(n: u32) -> (s: u32)
    ensures 
        s == sum_ints(n as int),
        s == n * (n + 1) / 2;
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
        invariant i <= n;
        invariant (acc as int) == sum_ints(i as int);
        decreases n - i;
    {
        proof {
            assert((acc as int) == sum_ints(i as int));
            sum_ints_succ_u32(i);
            assert((acc as int) + ((i as int) + 1) == sum_ints((i as int) + 1));
        }
        acc = acc + (i + 1);
        i = i + 1;
    }
    proof {
        assert(!(i < n));
        assert(i <= n);
        assert(i >= n);
        assert(i == n);
        assert((acc as int) == sum_ints(i as int));
        sum_ints_formula(n as int);
        assert((acc as int) == sum_ints(n as int));
    }
    acc
}
// </vc-code>

fn main() {
}

}