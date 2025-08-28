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
    requires 0 <= i <= arr.len()
    ensures arr.take(i).filter(|x: u32| x % 2 == 0) == arr.filter(|x: u32| x % 2 == 0).take(arr.take(i).filter(|x: u32| x % 2 == 0).len() as int)
    decreases i
{
    if i == 0 {
    } else {
        lemma_take_filter_prefix(arr, i - 1);
        assert(arr.take(i) == arr.take(i - 1).push(arr[i - 1]));
    }
}

proof fn lemma_all_even_prefix(arr: Seq<u32>, i: int)
    requires 
        0 <= i <= arr.len(),
        forall|k: int| 0 <= k < i ==> arr[k] % 2 == 0
    ensures arr.take(i) == arr.take(i).filter(|x: u32| x % 2 == 0)
    decreases i
{
    if i == 0 {
        assert(arr.take(0) == Seq::<u32>::empty());
        assert(arr.take(0).filter(|x: u32| x % 2 == 0) == Seq::<u32>::empty());
    } else {
        lemma_all_even_prefix(arr, i - 1);
        assert(arr[i - 1] % 2 == 0);
        assert(arr.take(i) == arr.take(i - 1).push(arr[i - 1]));
        assert(arr.take(i).filter(|x: u32| x % 2 == 0) == arr.take(i - 1).filter(|x: u32| x % 2 == 0).push(arr[i - 1]));
        assert(arr.take(i - 1).filter(|x: u32| x % 2 == 0) == arr.take(i - 1));
        assert(arr.take(i).filter(|x: u32| x % 2 == 0) == arr.take(i - 1).push(arr[i - 1]));
        assert(arr.take(i).filter(|x: u32| x % 2 == 0) == arr.take(i));
    }
}

proof fn lemma_all_even_implies_filter(arr: Seq<u32>)
    requires forall|k: int| 0 <= k < arr.len() ==> arr[k] % 2 == 0
    ensures arr == arr.filter(|x: u32| x % 2 == 0)
{
    lemma_all_even_prefix(arr, arr.len() as int);
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
            forall|k: int| 0 <= k < i ==> (arr[k] % 2 == 0)
        decreases arr.len() - i
    {
        if arr[i] % 2 != 0 {
            proof {
                lemma_all_even_prefix(arr@, i as int);
            }
            return Some(i);
        }
        i += 1;
    }
    proof {
        lemma_all_even_implies_filter(arr@);
    }
    None
}
// </vc-code>

} // verus!

fn main() {}