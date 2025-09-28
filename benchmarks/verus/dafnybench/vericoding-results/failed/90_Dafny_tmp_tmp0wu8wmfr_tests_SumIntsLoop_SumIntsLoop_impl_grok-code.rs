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
// <vc-helpers>

// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sum_ints_loop(n: u32) -> (s: u32)
    ensures 
        s == sum_ints(n as int),
        s == n * (n + 1) / 2;
// </vc-spec>
// <vc-code>
{
    let mut sum: u32 = 0;
    let mut i: u32 = n;
    proof {
        assert(sum as int == sum_ints(n as int) - sum_ints(i as int));
    }
    while i > 0 {
        invariant!(sum as int == sum_ints(n as int) - sum_ints(i as int));
        invariant!(i <= n);
        invariant!(i >= 0);
        decreases!(i);
        sum = sum + i;
        i = i - 1;
        proof {
            assert(sum as int == sum_ints(n as int) - sum_ints(i as int));
        }
    }
    sum
}
// </vc-code>

fn main() {
}

}