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
/* helper modified by LLM (iteration 2): Added decreases clause to the while loop to ensure termination. */
fn count_frequency(arr: &Vec<i32>, key: i32) -> (count: usize)
    requires
        arr.len() < usize::MAX,
    ensures
        count as int == count_frequency_rcr(arr@, key),
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            count as int == count_frequency_rcr(arr@.subrange(0, i as int), key),
        decreases arr.len() - i,
    {
        if arr[i] == key {
            count = count + 1;
        }
        i = i + 1;
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
/* code modified by LLM (iteration 2): Added decreases clause to the while loop to ensure termination. */
{
    let mut unique_arr = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            unique_arr@ == arr@.subrange(0, i as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
        decreases arr.len() - i,
    {
        let elem = arr[i];
        let count = count_frequency(arr, elem);
        if count == 1 {
            unique_arr.push(elem);
        }
        i = i + 1;
    }
    unique_arr
}
// </vc-code>

}
fn main() {}