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
/* helper modified by LLM (iteration 5): Fixed integer literal suffixes and simplified helpers */
prove fn count_frequency_lemma(seq: Seq<i32>, key: i32)
    ensures count_frequency_rcr(seq, key) == count_frequency_rcr(seq.drop_last(), key) + (if seq.last() == key {1} else {0})
{
    if seq.len() > 0 {
    }
}

spec fn is_unique_in_seq(seq: Seq<i32>, key: i32) -> bool {
    count_frequency_rcr(seq, key) == 1
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)

    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed integer literal comparison */
{
    let mut unique_arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            forall|j: int| 0 <= j < unique_arr@.len() ==> is_unique_in_seq(arr@, unique_arr@[j]),
            unique_arr@ == arr@.subrange(0, i as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1)
    {
        let elem = arr[i];
        proof {
            count_frequency_lemma(arr@, elem);
        }
        if count_frequency_rcr(arr@, elem) == 1 {
            unique_arr.push(elem);
        }
        i += 1;
    }
    unique_arr
}
// </vc-code>

}
fn main() {}