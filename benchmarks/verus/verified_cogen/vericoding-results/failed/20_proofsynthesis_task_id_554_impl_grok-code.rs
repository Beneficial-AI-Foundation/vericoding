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
    /* code modified by LLM (iteration 5): Fixed compilation error by inlining lambda in invariant instead of referencing helper spec fn for filter method */
    let mut result: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0),
            i <= arr.len()
        decreases (arr.len() - i) as int
    {
        if arr[i] % 2 != 0 {
            result.push(arr[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}