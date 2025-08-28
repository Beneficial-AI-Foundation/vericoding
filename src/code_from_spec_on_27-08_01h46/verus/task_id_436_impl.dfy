use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    // post-conditions-start
    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut negative_list = Vec::new();
    
    for i in 0..arr.len()
        invariant
            negative_list@ == arr@.subrange(0, i as int).filter(|x: i32| x < 0),
    {
        if arr[i] < 0 {
            negative_list.push(arr[i]);
        }
    }
    
    negative_list
}
// </vc-code>

} // verus!

fn main() {}