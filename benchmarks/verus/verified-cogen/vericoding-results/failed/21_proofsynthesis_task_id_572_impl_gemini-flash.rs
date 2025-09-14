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
/* helper modified by LLM (iteration 5): Adding a specification function for counting. */
spec fn count_occurrences(s: Seq<i32>, val: i32) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.last() == val {
        count_occurrences(s.drop_last(), val) + 1
    } else {
        count_occurrences(s.drop_last(), val)
    }
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)

    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Modified and simplified the loops into one loop. */{
    let mut unique_arr = Vec::<i32>::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i && i <= arr.len(),
            forall|k: int| 0 <= k < unique_arr.len() ==> count_occurrences(arr@, unique_arr@[k]) == 1,
            unique_arr@.len() <= i,
    {
        let cell = arr[i];
        if count_frequency_rcr(arr@, cell) == 1 {
            unique_arr.push(cell);
        }
        i = i + 1;
    }
    unique_arr
}
// </vc-code>

}
fn main() {}