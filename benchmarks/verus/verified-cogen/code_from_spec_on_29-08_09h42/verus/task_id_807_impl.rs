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
// pure-end

// <vc-helpers>
proof fn lemma_take_filter_property(arr: &Vec<u32>, idx: usize)
    requires idx < arr.len(),
             forall|k: int| 0 <= k < idx ==> arr[k] % 2 == 0,
    ensures arr@.take(idx as int) == arr@.take(idx as int).filter(|x: u32| x % 2 == 0),
{
    let take_seq = arr@.take(idx as int);
    let filtered_seq = take_seq.filter(|x: u32| x % 2 == 0);
    
    assert(take_seq.len() == idx);
    /* code modified by LLM (iteration 5): added missing 'by' clause */
    assert forall|i: int| 0 <= i < take_seq.len() implies take_seq[i] % 2 == 0 by {
        assert(take_seq[i] == arr[i]);
    };
    
    /* code modified by LLM (iteration 4): removed non-existent lemma call and simplified proof */
    assert(take_seq.len() == filtered_seq.len()) by {
        assert forall|i: int| 0 <= i < take_seq.len() implies take_seq[i] % 2 == 0;
    };
    
    assert forall|i: int| 0 <= i < take_seq.len() implies #[trigger] take_seq[i] == filtered_seq[i] by {
        assert(take_seq[i] % 2 == 0);
    };
    
    assert(take_seq =~= filtered_seq);
}

proof fn lemma_all_even_up_to_index(arr: &Vec<u32>, i: usize, j: usize)
    requires i <= j,
             forall|k: int| 0 <= k < i ==> arr[k] % 2 == 0,
             i < arr.len() && arr[i as int] % 2 == 0,
    ensures forall|k: int| 0 <= k <= i ==> arr[k] % 2 == 0,
{
}
// </vc-helpers>

// <vc-spec>
fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)
    // post-conditions-start
    ensures check_find_first_odd(arr, index),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut i = 0;
    
    /* code modified by LLM (iteration 2): added decreases clause to fix verification error */
    while i < arr.len()
        invariant 
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < i ==> arr[k] % 2 == 0,
        decreases arr.len() - i,
    {
        if arr[i] % 2 != 0 {
            proof {
                lemma_take_filter_property(arr, i);
            }
            return Some(i);
        }
        
        proof {
            lemma_all_even_up_to_index(arr, i, i);
        }
        
        i += 1;
    }
    
    None
}
// </vc-code>

} // verus!

fn main() {}