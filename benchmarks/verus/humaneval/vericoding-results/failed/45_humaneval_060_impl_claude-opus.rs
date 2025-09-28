// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn sum_from_one_to_n(n: int) -> int
    recommends n >= 1
{
    n * (n + 1) / 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed arithmetic proof in sum_lemma */
proof fn sum_lemma(n: int)
    requires
        n >= 1,
    ensures
        sum_from_one_to_n(n) == if n == 1 { 1 } else { sum_from_one_to_n(n - 1) + n },
    decreases n,
{
    if n == 1 {
        assert(sum_from_one_to_n(1) == 1 * 2 / 2 == 1);
    } else {
        sum_lemma(n - 1);
        assert(sum_from_one_to_n(n - 1) == (n - 1) * n / 2);
        assert(sum_from_one_to_n(n) == n * (n + 1) / 2);
        assert((n - 1) * n / 2 + n == n * (n + 1) / 2) by {
            assert((n - 1) * n + 2 * n == n * (n - 1 + 2));
            assert(n * (n - 1 + 2) == n * (n + 1));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_to_n(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == sum_from_one_to_n(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): corrected loop invariant and added overflow bounds */
    let mut sum: i8 = 0;
    let mut i: i8 = 1;
    
    assert(n as int <= 127);
    assert(sum_from_one_to_n(n as int) == n as int * (n as int + 1) / 2);
    assert(sum_from_one_to_n(n as int) <= 127 * 128 / 2);
    
    while i <= n
        invariant
            1 <= i as int,
            i as int <= n as int + 1,
            sum as int == sum_from_one_to_n((i - 1) as int),
            valid_input(n as int),
            n as int <= 127,
            sum as int >= 0,
            sum as int <= 127 * 128 / 2,
        decreases (n - i + 1) as int,
    {
        proof {
            sum_lemma(i as int);
            assert(sum_from_one_to_n(i as int) == sum_from_one_to_n((i - 1) as int) + i as int);
            assert(sum as int + i as int == sum_from_one_to_n(i as int));
            assert(sum_from_one_to_n(i as int) <= sum_from_one_to_n(n as int));
            assert(sum as int + i as int <= 127 * 128 / 2);
        }
        sum = sum + i;
        i = i + 1;
    }
    
    assert(i == n + 1);
    assert(sum as int == sum_from_one_to_n(n as int));
    
    sum
}
// </vc-code>


}

fn main() {}