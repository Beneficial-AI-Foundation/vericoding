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
    let mut odd_list = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            odd_list@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0),
        decreases arr.len() - i,
    {
        if arr[i] % 2 != 0 {
            odd_list.push(arr[i]);
            proof {
                assert(arr@.subrange(0, (i + 1) as int) == arr@.subrange(0, i as int).push(arr@[i as int]));
                assert(arr@.subrange(0, (i + 1) as int).filter(|x: u32| x % 2 != 0) == 
                       arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0).push(arr@[i as int]));
                assert(odd_list@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0).push(arr@[i as int]));
                assert(odd_list@ == arr@.subrange(0, (i + 1) as int).filter(|x: u32| x % 2 != 0));
            }
        } else {
            proof {
                assert(arr@.subrange(0, (i + 1) as int) == arr@.subrange(0, i as int).push(arr@[i as int]));
                assert(arr@.subrange(0, (i + 1) as int).filter(|x: u32| x % 2 != 0) == 
                       arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0));
                assert(odd_list@ == arr@.subrange(0, (i + 1) as int).filter(|x: u32| x % 2 != 0));
            }
        }
        i += 1;
    }
    proof {
        assert(i == arr.len());
        assert(arr@.subrange(0, i as int) == arr@);
    }
    odd_list
}
// </vc-code>

} // verus!

fn main() {}