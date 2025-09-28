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
/* helper modified by LLM (iteration 5): added parentheses to ensures clause and adjusted formatting to fix compilation error */
exec fn exec_count_frequency(seq: &Vec<i32>, key: i32) -> usize
    ensures( result as int == count_frequency_rcr(seq@, key) )
{
    let mut count = 0usize;
    let mut i = 0usize;
    while i < seq.len()
        invariant
            0 <= i <= seq.len(),
            count as int == count_frequency_rcr(seq@.take(i as int), key)
    {
        if seq[i] == key {
            count += 1;
        }
        i += 1;
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
/* code modified by LLM (iteration 5): no changes needed */
{
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result@ == arr@.take(i as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1)
    {
        let elem = arr[i];
        if exec_count_frequency(arr, elem) == 1 {
            result.push(elem);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}