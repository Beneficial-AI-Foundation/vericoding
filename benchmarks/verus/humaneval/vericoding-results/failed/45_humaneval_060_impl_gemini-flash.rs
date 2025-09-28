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
/* helper modified by LLM (iteration 5): fixed compilation error by removing `auto` */
lemma fn lemma_sum_inductive(k: int)
    requires k >= 1
    ensures sum_from_one_to_n(k) == sum_from_one_to_n(k - 1) + k
{
    if k == 1 {
        assert(sum_from_one_to_n(1) == 1);
    } else {
        let sum_k_minus_1_val = (k - 1) * k / 2;
        let sum_k_val = k * (k + 1) / 2;
        assert(sum_k_val == sum_k_minus_1_val + k);
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_to_n(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == sum_from_one_to_n(n as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): removed unnecessary assertion in proof block at the end, fixed loop invariant */
{
    let mut i: i8 = 1;
    let mut sum: i8 = 0;

    while (i <= n)
        invariant
            1 <= i,
            i <= n + 1,
            sum as int == sum_from_one_to_n((i - 1) as int),
            n >= 1,
            n as int <= 16,
        decreases (n - i) as int
    {
        proof {
            if i > 1 {
                lemma_sum_inductive((i - 1) as int);
            }
        }
        sum = sum + i;
        i = i + 1;
    }

    proof {
        lemma_sum_inductive(n as int);
    }

    sum
}
// </vc-code>


}

fn main() {}