// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): kept helper as an axiom */
proof fn lemma_exists_on_push(s: Seq<i32>, val: i32)
    requires
        s.len() >= 1,
    ensures
        (exists|j: int| 1 <= j < s.push(val).len() && s.push(val)[j] < 0)
        ==
        ((exists|j: int| 1 <= j < s.len() && s[j] < 0) || val < 0),
{}
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: &Vec<i32>) -> (result: (Vec<i32>, bool))
    ensures
        result.0.len() == operations.len() + 1,
        result.0[0] == 0,
        forall|i: int| 0 <= i < operations.len() ==> result.0[i + 1] == result.0[i] + operations[i],
        result.1 == (exists|i: int| 1 <= i < result.0.len() && result.0[i] < 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation errors by correcting `old()` syntax */
    let mut sums: Vec<i32> = Vec::new();
    sums.push(0);
    let mut is_below_zero = false;

    let mut i: usize = 0;
    while i < operations.len()
        invariant
            0 <= (i as int) <= (operations.len() as int),
            sums.len() == (i as int) + 1,
            sums[0] == 0,
            is_below_zero == (exists|j: int| 1 <= j < sums.len() && sums[j] < 0),
            forall|j: int| 0 <= j < (i as int) ==> sums[j + 1] == sums[j] + operations[j],
        decreases operations.len() - i
    {
        let current_sum = sums[i];
        let op = operations[i];
        let next_sum = current_sum + op;

        sums.push(next_sum);

        if next_sum < 0 {
            is_below_zero = true;
        }

        proof {
            let old_sums_view = old(sums).view();
            lemma_exists_on_push(old_sums_view, next_sum);
            assert(is_below_zero == (old(is_below_zero) || (next_sum < 0)));
        }

        i = i + 1;
    }

    (sums, is_below_zero)
}
// </vc-code>

}
fn main() {}