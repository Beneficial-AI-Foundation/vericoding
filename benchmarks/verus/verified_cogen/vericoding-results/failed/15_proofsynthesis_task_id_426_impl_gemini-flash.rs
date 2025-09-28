// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes required */
// </vc-helpers>

// <vc-spec>
fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)

    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added a `decreases` clause to the `while` loop */
{
    let mut odd_list: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            odd_list@ == arr@.take(i as int).filter(|x: u32| x % 2 != 0),
        decreases arr.len() - i
    {
        let num = arr[i];
        if num % 2 != 0 {
            odd_list.push(num);
        }
        i = i + 1;
    }
    odd_list
}
// </vc-code>

}
fn main() {}