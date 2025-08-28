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
proof fn lemma_take_filter_prefix(arr: Seq<u32>, i: int)
    requires 0 <= i < arr.len(),
             arr[i] % 2 != 0,
             forall|k: int| 0 <= k < i ==> arr[k] % 2 == 0,
    ensures arr.take(i) == arr.take(i).filter(|x: u32| x % 2 == 0)
{
    let prefix = arr.take(i);
    let filtered = prefix.filter(|x: u32| x % 2 == 0);
    
    assert forall|k: int| 0 <= k < prefix.len() implies prefix[k] % 2 == 0 by {
        assert(prefix[k] == arr[k]);
    };
    
    assert(prefix =~= filtered);
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
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < i ==> arr[k] % 2 == 0,
    {
        if arr[i] % 2 != 0 {
            proof {
                lemma_take_filter_prefix(arr@, i as int);
            }
            return Some(i);
        }
        i += 1;
    }
    None
}
// </vc-code>

} // verus!

fn main() {}