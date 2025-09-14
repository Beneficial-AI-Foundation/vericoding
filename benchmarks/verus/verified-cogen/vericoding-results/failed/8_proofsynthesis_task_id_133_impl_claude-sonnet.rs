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
/* helper modified by LLM (iteration 5): fixed proof function syntax with proper braces */
spec fn sum_negative_to_partial(seq: Seq<i64>, i: int) -> int
    decreases seq.len() - i,
{
    if i == seq.len() {
        0
    } else {
        sum_negative_to_partial(seq, i + 1) + if seq[i] < 0 { seq[i] as int } else { 0 }
    }
}

proof fn sum_negative_equivalence(seq: Seq<i64>)
    decreases seq.len(),
    ensures sum_negative_to(seq) == sum_negative_to_partial(seq, 0),
{
    if seq.len() == 0 {
        // Base case
    } else {
        sum_negative_equivalence(seq.drop_last());
        assert(sum_negative_to_partial(seq.drop_last(), 0) == sum_negative_to_partial(seq, 0) - if seq.last() < 0 { seq.last() as int } else { 0 });
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_negatives(arr: &Vec<i64>) -> (sum_neg: i128)

    ensures
        sum_negative_to(arr@) == sum_neg,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed invariant to use correct range */
    let mut sum: i128 = 0;
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            sum == sum_negative_to_partial(arr@, i as int),
    {
        if arr[i] < 0 {
            sum = sum + (arr[i] as i128);
        }
        i = i + 1;
    }
    
    proof {
        sum_negative_equivalence(arr@);
    }
    
    sum
}
// </vc-code>

}
fn main() {}