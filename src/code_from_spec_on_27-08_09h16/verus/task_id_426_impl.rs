use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn is_odd(x: u32) -> bool {
    x % 2 != 0
}

proof fn filter_subrange_extension_lemma(arr: Seq<u32>, i: nat)
    requires i < arr.len()
    ensures arr.subrange(0, i as int).filter(|x: u32| x % 2 != 0) == arr.subrange(0, (i + 1) as int).filter(|x: u32| x % 2 != 0) || 
            arr.subrange(0, (i + 1) as int).filter(|x: u32| x % 2 != 0) == arr.subrange(0, i as int).filter(|x: u32| x % 2 != 0).push(arr[i as int])
{
    let sub_i = arr.subrange(0, i as int);
    let sub_i_plus_1 = arr.subrange(0, (i + 1) as int);
    
    assert(sub_i_plus_1 == sub_i.push(arr[i as int]));
    
    if arr[i as int] % 2 != 0 {
        vstd::seq::seq_filter_lemma_push(sub_i, arr[i as int], |x: u32| x % 2 != 0);
    } else {
        vstd::seq::seq_filter_lemma_push(sub_i, arr[i as int], |x: u32| x % 2 != 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)
    // post-conditions-start
    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0),
        decreases arr.len() - i,
    {
        if arr[i] % 2 != 0 {
            result.push(arr[i]);
        }
        i += 1;
        
        proof {
            assert(arr@.subrange(0, (i - 1) as int).push(arr[(i - 1) as int]) == arr@.subrange(0, i as int));
        }
    }
    
    proof {
        assert(i == arr.len());
        assert(arr@.subrange(0, i as int) == arr@);
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}