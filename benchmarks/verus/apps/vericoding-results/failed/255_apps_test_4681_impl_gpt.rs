// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn lucas(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n <= 0 {
        2
    } else if n == 1 {
        1
    } else {
        lucas(n - 1) + lucas(n - 2)
    }
}

spec fn valid_input(n: int) -> bool {
    1 <= n <= 86
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added lemma for Lucas recurrence relation */
proof fn lucas_step(n: int)
    requires
        n >= 1,
    ensures
        lucas(n + 1) == lucas(n) + lucas(n - 1),
{
    assert(n + 1 > 1);
    assert(lucas(n + 1) == lucas(n) + lucas(n - 1));
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == lucas(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Use machine integers in exec code and relate to spec via casts; iterative Lucas computation with invariants */
    let ni: i32 = n as i32;

    // Initialize with L0 = 2, L1 = 1
    let mut i: i32 = 1;
    let mut a: i128 = 2;
    let mut b: i128 = 1;

    proof {
        assert(lucas(0) == 2);
        assert(lucas(1) == 1);
    }

    while i < ni
        invariant
            valid_input(ni as int),
            1 <= i as int,
            i as int <= ni as int,
            a as int == lucas(i as int - 1),
            b as int == lucas(i as int),
        decreases ni as int - i as int
    {
        let next: i128 = a + b;
        proof {
            lucas_step(i as int);
            assert(lucas(i as int + 1) == lucas(i as int) + lucas(i as int - 1));
            assert(next as int == a as int + b as int);
        }
        a = b;
        b = next;
        i = i + 1;
    }

    let res: i128 = b; // i == ni, so b corresponds to lucas(ni)
    let result: i8 = res as i8;
    result
}
// </vc-code>


}

fn main() {}