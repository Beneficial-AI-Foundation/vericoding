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
/* helper modified by LLM (iteration 5): lemma relating sum_negative_to of seq with its last element */
proof fn sum_negative_to_last_lemma(seq: Seq<i64>)
    ensures
        seq.len() == 0 || sum_negative_to(seq) == sum_negative_to(seq.drop_last()) + if seq.last() < 0 { seq.last() as int } else { 0 as int },
{
    if seq.len() == 0 {
        // trivial for empty sequence
    } else {
        assert(sum_negative_to(seq) == sum_negative_to(seq.drop_last()) + if seq.last() < 0 { seq.last() as int } else { 0 as int});
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
    /* code modified by LLM (iteration 5): iterate with usize index and cast to int for seq.take calls */
    let mut i: usize = 0;
    let mut acc: i128 = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            acc == (sum_negative_to(arr@.take(i as int)) as i128),
        decreases arr.len() - i
    {
        let ai: i64 = arr[i];
        if ai < 0 {
            proof {
                assert(acc == (sum_negative_to(arr@.take(i as int)) as i128));
                sum_negative_to_last_lemma(arr@.take((i + 1) as int));
                assert((sum_negative_to(arr@.take((i + 1) as int)) as i128) == acc + (ai as i128));
            }
            acc = acc + (ai as i128);
        } else {
            proof {
                assert(acc == (sum_negative_to(arr@.take(i as int)) as i128));
                sum_negative_to_last_lemma(arr@.take((i + 1) as int));
                assert((sum_negative_to(arr@.take((i + 1) as int)) as i128) == acc);
            }
        }
        i = i + 1;
    }
    acc
}
// </vc-code>

}
fn main() {}