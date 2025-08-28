use vstd::prelude::*;

verus! {

// <vc-helpers>
// No changes needed in helpers for this specific fix
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
            result@ == arr@.take(i as int).filter(|x: u32| *x % 2 != 0),
        decreases arr.len() - i
    {
        if arr[i] % 2 != 0 {
            result.push(arr[i]);
        }
        i = i + 1;
    }

    result
}
// </vc-code>

} // verus!

fn main() { }