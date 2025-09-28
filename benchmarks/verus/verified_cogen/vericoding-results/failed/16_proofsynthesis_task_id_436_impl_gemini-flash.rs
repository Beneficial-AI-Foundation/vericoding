// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed as no helper functions are needed. Also added a `subsequence` function for `Seq<T>` */
        proof fn subsequence<T>(s: Seq<T>, start: int, end: int) -> Seq<T>
        requires
            0 <= start <= end <= s.len(),
        ensures
            s.subsequence(start, end) == Seq::new().push_seq(s.skip(start).take(end - start)),
        {
            s.skip(start).take(end - start)
        }
// </vc-helpers>

// <vc-spec>
fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)

    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed `subsequence` calls by introducing a helper function, and also handled the proof for `filter` and `push` operations. */
{
    let mut negative_list: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i && i <= arr.len(),
            negative_list@ == subsequence(arr@, 0, i as int).filter(|x: i32| x < 0),
    {
        if arr[i] < 0 {
            proof {
                let old_negative_list_seq = negative_list@;
                assert(old_negative_list_seq.ext_equal(subsequence(arr@, 0, i as int).filter(|x: i32| x < 0)));
                assert(old_negative_list_seq.push(arr[i]) =~= subsequence(arr@, 0, (i + 1) as int).filter(|x: i32| x < 0));
            }
            negative_list.push(arr[i]);
        }
        i = i + 1;
    }
    proof {
        assert(negative_list@ == subsequence(arr@, 0, arr.len() as int).filter(|x: i32| x < 0));
        assert(arr@.filter(|x: i32| x < 0) =~= subsequence(arr@, 0, arr.len() as int).filter(|x: i32| x < 0));
    }
    negative_list
}
// </vc-code>

}
fn main() {}