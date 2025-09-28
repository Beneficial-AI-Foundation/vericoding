// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_odd(x: u32) -> bool { x % 2 != 0 }
// </vc-helpers>

// <vc-spec>
fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)

    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
// </vc-spec>
// <vc-code>
{
    let mut odd_list: Vec<u32> = Vec::new();
    let mut i: nat = 0;
    while i < arr@.len()
        invariant
            i <= arr@.len(),
            odd_list@ == arr@.take(i).filter(|x| x % 2 != 0),
        decreases arr@.len() - i
    {
        let val = arr@[i];
        if val % 2 != 0 {
            odd_list.push(val);
        }
        i = i + 1;
    }
    odd_list
}
// </vc-code>

}
fn main() {}