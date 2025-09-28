// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for odd numbers */
spec fn is_odd(x: u32) -> bool { x % 2 != 0 }
// </vc-helpers>

// <vc-spec>
fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)

    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build odd_list by iterating and maintaining ghost invariant using slice and spec predicate */
    let mut odd_list: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            odd_list@ == arr@.slice(0, i as nat).filter(|x: u32| is_odd(x)),
        decreases arr.len() - i
    {
        let val: u32 = arr[i];
        if val % 2 != 0 {
            odd_list.push(val);
        }
        i += 1;
    }
    proof {
        assert(arr@.slice(0, arr.len() as nat) == arr@);
        assert(odd_list@ == arr@.filter(|x: u32| is_odd(x)));
    }
    odd_list
}
// </vc-code>

}
fn main() {}