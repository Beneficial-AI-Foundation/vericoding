// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_ones_in_octal(a: int) -> int
    decreases a when a >= 0
{
    if a == 0 {
        0int
    } else {
        (if a % 8 == 1 { 1int } else { 0int }) + count_ones_in_octal(a / 8)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added lemma for tighter bound and fixed proof */
proof fn count_nonnegative(x: int)
    requires x >= 0
    ensures count_ones_in_octal(x) >= 0
    decreases x
{
    if x > 0 {
        count_nonnegative(x / 8);
    }
}

proof fn count_bound_for_16(x: int)
    requires 0 <= x < 16
    ensures count_ones_in_octal(x) <= 2
    decreases x
{
    if x > 0 {
        let q = x / 8;
        assert(q <= 1);
        count_bound_for_16(q);

        if q == 1 {
            count_bound_for_16(0);
            assert(count_ones_in_octal(1) == 1);
        } else {
            assert(count_ones_in_octal(0) == 0);
        }
        assert(count_ones_in_octal(q) <= 1);
    }
}

proof fn count_bound_for_i8(x: int)
    requires 0 <= x < 128
    ensures count_ones_in_octal(x) <= 3
    decreases x
{
    if x > 0 {
        let q = x / 8;
        assert(q < 16);
        count_bound_for_16(q);
        assert(count_ones_in_octal(q) <= 2);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8) -> (count: i8)
    requires 
        a >= 0,
    ensures 
        count >= 0,
        count as int == count_ones_in_octal(a as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): No change to code, fix is in helpers */
    let mut n = a;
    let mut count: i8 = 0;

    proof {
        count_bound_for_i8(a as int);
    }

    while n > 0
        invariant
            n >= 0,
            count >= 0,
            count_ones_in_octal(a as int) == count as int + count_ones_in_octal(n as int),
            count_ones_in_octal(a as int) <= 3,
        decreases n
    {
        proof {
            count_nonnegative(n as int);
        }

        if n % 8 == 1 {
            count = count + 1;
        }
        n = n / 8;
    }
    count
}
// </vc-code>


}

fn main() {}