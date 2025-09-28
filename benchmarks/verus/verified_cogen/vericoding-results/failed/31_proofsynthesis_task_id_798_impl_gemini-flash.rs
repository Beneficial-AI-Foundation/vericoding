// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_to(arr: Seq<i64>) -> (result: int)
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove seq_to_vec_subsequence helper because it compiles with `subsequence` */
// </vc-helpers>

// <vc-spec>
fn sum(arr: &Vec<i64>) -> (result: i128)

    ensures
        sum_to(arr@) == result
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): add decreases clause to while loop */
{
    let mut total: i128 = 0;
    let mut i: usize = 0;

    while i < arr.len()
        invariant
            total == sum_to(arr@.take(i as int)),
            i <= arr.len()
        decreases arr.len() - i
    {
        total = total + arr[i] as i128;
        i = i + 1;
    }
    total
}
// </vc-code>

}
fn main() {}