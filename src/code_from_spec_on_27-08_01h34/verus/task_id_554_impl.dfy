use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
    // post-conditions-start
    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0),
    {
        if arr[i] % 2 != 0 {
            result.push(arr[i]);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

} // verus!

fn main() { }