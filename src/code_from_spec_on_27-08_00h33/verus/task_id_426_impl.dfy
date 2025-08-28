use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn is_odd(x: u32) -> bool {
    x % 2 != 0
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
            proof {
                let old_result = result@.drop_last();
                assert(old_result == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0));
                assert(result@.last() == arr[i]);
                assert(arr[i] % 2 != 0);
                assert(result@ == old_result.push(arr[i]));
                assert(arr@.subrange(0, (i + 1) as int) == arr@.subrange(0, i as int).push(arr[i]));
            }
        } else {
            proof {
                assert(arr[i] % 2 == 0);
                assert(result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0));
                assert(arr@.subrange(0, (i + 1) as int) == arr@.subrange(0, i as int).push(arr[i]));
            }
        }
        i += 1;
    }
    
    proof {
        assert(i == arr.len());
        assert(arr@.subrange(0, i as int) =~= arr@);
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}