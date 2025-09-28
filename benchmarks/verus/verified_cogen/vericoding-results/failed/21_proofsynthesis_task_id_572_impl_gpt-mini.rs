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
/* helper modified by LLM (iteration 5): is_unique spec wrapper */
spec fn is_unique(seq: Seq<i32>, key: i32) -> bool { count_frequency_rcr(seq, key) == 1 }
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)

    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute frequency via nested loops without ghost mut, maintain invariants relating runtime counts to spec */
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            res@ == arr@.slice(0, i as nat).filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
        decreases arr.len() - i
    {
        let mut freq: usize = 0;
        let mut j: usize = 0;
        while j < arr.len()
            invariant
                j <= arr.len(),
                freq as int == count_frequency_rcr(arr@.slice(0, j as nat), arr@[i as nat]),
            decreases arr.len() - j
        {
            if arr[j] == arr[i] {
                freq = freq + 1;
            }
            j = j + 1;
        }
        proof {
            assert(freq as int == count_frequency_rcr(arr@, arr@[i as nat]));
        }
        if freq == 1 {
            res.push(arr[i]);
        }
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}