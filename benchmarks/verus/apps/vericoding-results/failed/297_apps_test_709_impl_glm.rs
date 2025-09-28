// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_ones_in_binary(n: int) -> int
    recommends n >= 1
    decreases n
    when n >= 1
{
    if n == 1 {
        1
    } else if n % 2 == 1 {
        1 + count_ones_in_binary(n / 2)
    } else {
        count_ones_in_binary(n / 2)
    }
}

spec fn valid_input(x: int) -> bool {
    x >= 1
}

spec fn valid_output(x: int, result: int) -> bool {
    valid_input(x) && result == count_ones_in_binary(x)
}
// </vc-preamble>

// <vc-helpers>
spec fn count_ones_in_binary_nonneg(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n == 0 {
        0
    } else {
        if n % 2 == 1 {
            1 + count_ones_in_binary_nonneg(n / 2)
        } else {
            count_ones_in_binary_nonneg(n / 2)
        }
    }
}

proof fn lemma_count_ones_equivalent(n: int)
    requires n >= 1
    ensures count_ones_in_binary_nonneg(n) == count_ones_in_binary(n)
    decreases n
{
    if n == 1 {
        assert(count_ones_in_binary_nonneg(1) == 1);
        assert(count_ones_in_binary(1) == 1);
    } else if n % 2 == 1 {
        lemma_count_ones_equivalent(n / 2);
        assert(count_ones_in_binary_nonneg(n) == 1 + count_ones_in_binary_nonneg(n / 2));
        assert(count_ones_in_binary(n) == 1 + count_ones_in_binary(n / 2));
        assert(count_ones_in_binary_nonneg(n / 2) == count_ones_in_binary(n / 2));
    } else {
        lemma_count_ones_equivalent(n / 2);
        assert(count_ones_in_binary_nonneg(n) == count_ones_in_binary_nonneg(n / 2));
        assert(count_ones_in_binary(n) == count_ones_in_binary(n / 2));
        assert(count_ones_in_binary_nonneg(n / 2) == count_ones_in_binary(n / 2));
    }
}
// </vc-helpers>

// <vc-spec>
fn min_bacteria(x: i8) -> (result: i8)
    requires valid_input(x as int)
    ensures valid_output(x as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): changed n and count to i32 to fix int type usage in exec code */
    let mut n = x as i32;
    let mut count: i32 = 0;
    while n > 0
        invariant
            n >= 0,
            (count as int) + count_ones_in_binary_nonneg(n as int) == count_ones_in_binary_nonneg(x as int),
        decreases n
    {
        if n % 2 == 1 {
            count += 1;
        }
        n = n / 2;
    }
    proof {
        lemma_count_ones_equivalent(x as int);
    }
    count as i8
}
// </vc-code>


}

fn main() {}