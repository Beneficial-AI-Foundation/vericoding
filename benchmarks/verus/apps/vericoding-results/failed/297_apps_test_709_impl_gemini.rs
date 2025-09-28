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
/* helper modified by LLM (iteration 2): added explicit case analysis for induction proof */
spec fn count_ones_non_neg(n: int) -> int
    recommends n >= 0
    decreases n
    when n >= 0
{
    if n == 0 {
        0
    } else if n % 2 == 1 {
        1 + count_ones_non_neg(n / 2)
    } else {
        count_ones_non_neg(n / 2)
    }
}

proof fn lemma_count_equiv(n: int)
    requires
        n >= 1,
    ensures
        count_ones_in_binary(n) == count_ones_non_neg(n),
    decreases n
{
    if n > 1 {
        lemma_count_equiv(n / 2);
    }
}
// </vc-helpers>

// <vc-spec>
fn min_bacteria(x: i8) -> (result: i8)
    requires valid_input(x as int)
    ensures valid_output(x as int, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added proof block and an explicit invariant to prevent overflow */
{
    proof {
        lemma_count_equiv(x as int);
    }

    let mut count: i8 = 0;
    let mut current_x = x;

    while current_x > 0
        invariant
            valid_input(x as int),
            current_x >= 0,
            count >= 0,
            x as int <= 127 ==> count <= 7,
            count_ones_in_binary(x as int) == count_ones_non_neg(x as int),
            count_ones_non_neg(x as int) == (count as int) + count_ones_non_neg(current_x as int),
        decreases current_x
    {
        let prev_current_x = current_x;

        if current_x % 2 == 1 {
            count = count + 1;
        }
        current_x = current_x / 2;

        proof {
            if prev_current_x % 2 == 1 {
                assert(count_ones_non_neg(prev_current_x as int) == 1 + count_ones_non_neg(current_x as int));
            } else {
                assert(count_ones_non_neg(prev_current_x as int) == count_ones_non_neg(current_x as int));
            }
        }
    }

    count
}
// </vc-code>


}

fn main() {}