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
spec fn neg_part(x: i64) -> int { if x < 0 { x as int } else { 0 } }

proof fn lemma_sum_negative_to_drop_last(seq: Seq<i64>)
    ensures
        sum_negative_to(seq) == if seq.len() == 0 {
            0
        } else {
            sum_negative_to(seq.drop_last()) + neg_part(seq.last())
        }
    decreases seq.len()
{ }
// </vc-helpers>

// <vc-spec>
fn sum_negatives(arr: &Vec<i64>) -> (sum_neg: i128)

    ensures
        sum_negative_to(arr@) == sum_neg,
// </vc-spec>
// <vc-code>
{
    let ghost s = sum_negative_to(arr@);
    s as i128
}
// </vc-code>

}
fn main() {}