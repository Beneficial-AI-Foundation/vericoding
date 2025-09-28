// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_frequency_rcr(seq: Seq<i32>, key: i32) -> (result: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_frequency_rcr(seq.drop_last(), key) + if (seq.last() == key) {
            1 as int
        } else {
            0 as int
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed invariant to expression to fix compilation error */
fn count_frequency_non_ghost(arr: &Vec<i32>, x: i32) -> (count: i32)
    ensures count == count_frequency_rcr(arr@, x)
{
    let mut count = 0;
    ghost! {
        let mut prefix = Seq::empty();
    }
    for i in 0..arr.len()
        invariant (0 <= (i as int) <= arr@.len() && prefix == arr@.subrange(0, i as int) && count == count_frequency_rcr(prefix, x))
    {
        if arr[i] == x {
            count += 1;
        }
        ghost! {
            prefix = prefix.push(arr[i]);
        }
    }
    count
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)

    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no changes needed after helper compilation fix */
{
    let mut unique_arr = Vec::new();
    for i in 0..arr.len() {
        let x = arr[i];
        if count_frequency_non_ghost(arr, x) == 1 {
            unique_arr.push(x);
        }
    }
    unique_arr
}
// </vc-code>

}
fn main() {}