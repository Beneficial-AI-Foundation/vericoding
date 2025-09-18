// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn spec_sums(operations: Seq<i32>) -> Seq<i32>
    decreases operations.len()
{
    let len = operations.len();
    if len == 0 {
        seq![0]
    } else {
        let prev_sums = spec_sums(operations.drop_last());
        prev_sums.push(prev_sums[(len - 1) as int] + operations[(len - 1) as int])
    }
}
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
    /* code modified by LLM (iteration 5): Fixed `nat` and `int` type mismatches, and `Seq::sub_seq` method call */
    let mut current_sum: i32 = 0;
    let mut sums: Vec<i32> = Vec::new();
    sums.push(0);
    let mut is_below_zero: bool = false;

    let operations_len = operations.len();
    let mut i: usize = 0;
    while i < operations_len
        invariant
            i <= operations_len,
            sums.len() == i + 1,
            sums.len() > 0 && sums[0] == 0,
            is_below_zero == (exists|k: int| 1 <= k && k < (i as int) + 1 && sums[k as usize] < 0),
            forall|j: int| 0 <= j && j < (i as int) ==> sums[j as usize + 1] == sums[j as usize] + operations[j as usize],
            current_sum == sums[i as usize],
            sums.view() == spec_sums(operations.view().subsequence(0, i as int)),
        decreases operations_len - i
    {
        current_sum = current_sum + operations[i];
        sums.push(current_sum);

        if current_sum < 0 {
            is_below_zero = true;
        }
        i = i + 1;
    }

    (sums, is_below_zero)
}
// </vc-code>

}
fn main() {}