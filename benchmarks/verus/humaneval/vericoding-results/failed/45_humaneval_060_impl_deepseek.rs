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
/* helper modified by LLM (iteration 5): Removed proof blocks from lemma and added proper decreases clause */
proof fn lemma_sum_formula(k: int)
    requires
        k >= 0,
    ensures
        k * (k + 1) % 2 == 0,
        sum_from_one_to_n(k) == k * (k + 1) / 2
    decreases k
{
    if k > 0 {
        lemma_sum_formula(k - 1);
        assert((k * (k + 1)) % 2 == 0) by (nonlinear_arith);
    }
}

spec fn sum_property(n: int, current: int, acc: int) -> bool {
    &&& current <= n
    &&& acc == sum_from_one_to_n(n) - sum_from_one_to_n(current)
}
// </vc-helpers>

// <vc-spec>
fn sum_to_n(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == sum_from_one_to_n(n as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed proof block placement and added explicit decreases clause */
{
    let mut current: i8 = n;
    let mut acc: i8 = 0;
    
    proof { lemma_sum_formula(n as int); }
    
    while current > 0
        invariant
            current >= 0,
            acc as int == sum_from_one_to_n(n as int) - sum_from_one_to_n(current as int),
        decreases current as int
    {
        lemma_sum_formula(current as int);
        assert(current >= 1);
        let old_current = current;
        let old_acc = acc;
        acc = ((acc as i32) + (current as i32)) as i8;
        current = current - 1;
        proof {
            assert(acc as int == old_acc as int + old_current as int);
            assert(sum_from_one_to_n(old_current as int) - sum_from_one_to_n((old_current - 1) as int) == old_current as int);
            assert(acc as int == (sum_from_one_to_n(n as int) - sum_from_one_to_n(old_current as int)) + old_current as int);
            assert(acc as int == sum_from_one_to_n(n as int) - sum_from_one_to_n((old_current - 1) as int));
        }
    }
    
    assert(current == 0);
    proof { lemma_sum_formula(0); }
    acc
}
// </vc-code>


}

fn main() {}