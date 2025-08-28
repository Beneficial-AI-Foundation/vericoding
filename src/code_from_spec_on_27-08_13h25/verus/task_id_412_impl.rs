use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers in this case
// </vc-helpers>

// <vc-spec>
fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)
    // post-conditions-start
    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result: Vec<u32> = Vec::new();
    let mut i: usize = 0;

    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.take(i as int).filter(|x: u32| x % 2 == 0),
        decreases arr.len() - i
    {
        if arr@[i as int] % 2 == 0 {
            result.push(arr@[i as int]);
        }
        i = i + 1;
    }

    result
}
// </vc-code>

} // verus!

fn main() {}