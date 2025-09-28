// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_negative_to(seq: Seq<i64>) -> (res: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        sum_negative_to(seq.drop_last()) + if (seq.last() < 0) {
            seq.last() as int
        } else {
            0 as int
        }
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sum_negatives(arr: &Vec<i64>) -> (sum_neg: i128)

    ensures
        sum_negative_to(arr@) == sum_neg,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatches by casting i to int instead of nat for Seq methods */
    let mut sum: i128 = 0;
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            sum == sum_negative_to(arr@.take(i as int)),
            sum + sum_negative_to(arr@.subrange(i as int, arr@.len())) == sum_negative_to(arr@)
        decreases arr.len() - i
    {
        let val = arr[i];
        if val < 0 {
            sum = sum + (val as i128);
        }
        i = i + 1;
    }
    sum
}
// </vc-code>

}
fn main() {}