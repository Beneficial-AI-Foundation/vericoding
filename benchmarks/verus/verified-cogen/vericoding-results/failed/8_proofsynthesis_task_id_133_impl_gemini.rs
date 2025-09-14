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
proof fn sum_negative_to_append_lemma(s: Seq<i64>, x: i64)
    ensures sum_negative_to(s.push(x)) == sum_negative_to(s) + if x < 0 { x as int } else { 0 as int },
{
}
// </vc-helpers>

// <vc-spec>
fn sum_negatives(arr: &Vec<i64>) -> (sum_neg: i128)

    ensures
        sum_negative_to(arr@) == sum_neg,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to the while loop */
    let mut sum_neg: i128 = 0;
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            sum_neg as int == sum_negative_to(arr@.subrange(0, i as int)),
        decreases arr.len() - i,
    {
        let elt = arr[i];

        proof {
            sum_negative_to_append_lemma(arr@.subrange(0, i as int), elt);
        }

        if elt < 0 {
            sum_neg = sum_neg + (elt as i128);
        }

        i = i + 1;
    }
    sum_neg
}
// </vc-code>

}
fn main() {}