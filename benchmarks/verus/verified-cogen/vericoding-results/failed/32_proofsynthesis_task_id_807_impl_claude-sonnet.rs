// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn check_find_first_odd(arr: &Vec<u32>, index: Option<usize>) -> (result: bool)
{
    if let Some(idx) = index {
        &&& arr@.take(idx as int) == arr@.take(idx as int).filter(|x: u32| x % 2 == 0)
        &&& arr[idx as int] % 2 != 0
    } else {
        forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed proof by adding lemmas about sequence properties */
proof fn lemma_take_filter_even(arr: &Vec<u32>, i: usize)
    requires
        i <= arr.len(),
        forall|k: int| 0 <= k < i ==> arr[k] % 2 == 0,
    ensures
        arr@.take(i as int).filter(|x: u32| x % 2 == 0) =~= arr@.take(i as int),
{
    let take_seq = arr@.take(i as int);
    let filtered_seq = take_seq.filter(|x: u32| x % 2 == 0);
    
    assert forall|idx: int| 0 <= idx < take_seq.len() implies take_seq[idx] % 2 == 0 by {
        assert(take_seq[idx] == arr@[idx]);
        assert(0 <= idx < i);
    }
    
    assert(take_seq =~= filtered_seq) by {
        assert(take_seq.len() == i);
        assert forall|x: u32| take_seq.contains(x) ==> x % 2 == 0;
        
        assert(filtered_seq.len() <= take_seq.len());
        
        assert forall|idx: int| 0 <= idx < take_seq.len() implies #[trigger] take_seq[idx] % 2 == 0 by {
            assert(take_seq[idx] == arr@[idx]);
            assert(0 <= idx < i);
        }
        
        assert(take_seq.len() == filtered_seq.len()) by {
            assert forall|x: u32| take_seq.contains(x) ==> x % 2 == 0;
        }
        
        assert forall|idx: int| 0 <= idx < take_seq.len() implies take_seq[idx] == filtered_seq[idx] by {
            assert(take_seq[idx] % 2 == 0);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)

    ensures check_find_first_odd(arr, index),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): kept working implementation */
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < i ==> arr[k] % 2 == 0,
        decreases arr.len() - i
    {
        if arr[i] % 2 != 0 {
            proof {
                lemma_take_filter_even(arr, i);
            }
            return Some(i);
        }
        i += 1;
    }
    None
}
// </vc-code>

}
fn main() {}