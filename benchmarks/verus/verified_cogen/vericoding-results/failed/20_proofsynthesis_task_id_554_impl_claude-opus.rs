// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)

    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed ownership issue by not moving odd_numbers in loop */
    let mut odd_numbers = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            odd_numbers@ == arr@.take(i as int).filter(|x: u32| x % 2 != 0),
        decreases arr.len() - i,
    {
        let old_i = i;
        
        if arr[i] % 2 != 0 {
            let old_odd_numbers_view = odd_numbers@;
            odd_numbers.push(arr[i]);
            proof {
                assert(arr@.take(old_i as int + 1) == arr@.take(old_i as int).push(arr@[old_i as int]));
                assert(odd_numbers@ == old_odd_numbers_view.push(arr@[old_i as int]));
                assert(arr@[old_i as int] % 2 != 0);
                assert(odd_numbers@ == arr@.take(old_i as int + 1).filter(|x: u32| x % 2 != 0));
            }
        } else {
            proof {
                assert(arr@.take(old_i as int + 1) == arr@.take(old_i as int).push(arr@[old_i as int]));
                assert(arr@[old_i as int] % 2 == 0);
                assert(odd_numbers@ == arr@.take(old_i as int + 1).filter(|x: u32| x % 2 != 0));
            }
        }
        i = i + 1;
    }
    assert(arr@.take(arr.len() as int) == arr@);
    odd_numbers
}
// </vc-code>

}
fn main() {}