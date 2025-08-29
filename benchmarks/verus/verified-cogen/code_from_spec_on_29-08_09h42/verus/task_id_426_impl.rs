use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    
    /* code modified by LLM (iteration 5): add proof block to help verification */
    while i < arr.len()
        invariant
            i <= arr.len(),
            odd_list@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0),
        decreases arr.len() - i,
    {
        if arr[i] % 2 != 0 {
            odd_list.push(arr[i]);
        }
        i += 1;
        
        proof {
            assert(arr@.subrange(0, i as int) == arr@.subrange(0, (i - 1) as int).push(arr@[(i - 1) as int]));
        }
    }
    
    /* code modified by LLM (iteration 5): add proof to establish postcondition */
    proof {
        assert(i == arr.len());
        assert(arr@.subrange(0, i as int) == arr@);
    }
    
    odd_list
}
// </vc-code>

} // verus!

fn main() {}