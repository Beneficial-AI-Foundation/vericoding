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

// </vc-helpers>

// <vc-spec>
fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)

    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed int literal syntax errors */
    let mut unique_arr = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            unique_arr@ == arr@.take(i as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
            forall|k: int| 0 <= k < unique_arr.len() ==> count_frequency_rcr(arr@, unique_arr@[k]) == 1,
        decreases arr.len() - i,
    {
        let mut j: usize = 0;
        let mut count: int = 0int;
        while j < arr.len()
            invariant
                j <= arr.len(),
                i < arr.len(),
                count == count_frequency_rcr(arr@.take(j as int), arr@[i as int]),
                count >= 0,
            decreases arr.len() - j,
        {
            if arr[j] == arr[i] {
                count = count + 1int;
            }
            j = j + 1;
        }
        assert(arr@.take(arr.len() as int) == arr@);
        assert(count == count_frequency_rcr(arr@, arr@[i as int]));
        if count == 1int {
            unique_arr.push(arr[i]);
            assert(arr@.take((i + 1) as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1)
                == arr@.take(i as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1).push(arr@[i as int]));
        } else {
            assert(arr@.take((i + 1) as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1)
                == arr@.take(i as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1));
        }
        i = i + 1;
    }
    assert(arr@.take(arr.len() as int) == arr@);
    assert(unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1));
    unique_arr
}
// </vc-code>

}
fn main() {}