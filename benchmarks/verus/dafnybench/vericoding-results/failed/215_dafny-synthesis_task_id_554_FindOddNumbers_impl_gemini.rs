// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_odd_numbers(arr: &[i32]) -> (odd_list: Vec<i32>)

    ensures 
        forall|i: int| 0 <= i < odd_list.len() ==> is_odd(odd_list[i] as int) && arr@.contains(odd_list[i]),

        forall|i: int| 0 <= i < arr.len() && is_odd(arr[i] as int) ==> odd_list@.contains(arr[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): aligned if condition with is_odd spec */
    let mut odd_list: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < odd_list.len() ==> is_odd(odd_list[k] as int) && arr@.contains(odd_list[k]),
            forall|k: int| 0 <= k < i && is_odd(arr@[k] as int) ==> odd_list@.contains(arr@[k]),
        decreases arr.len() - i
    {
        let current = arr[i];
        if current % 2 == 1 {
            odd_list.push(current);
        }
        i = i + 1;
    }
    odd_list
}
// </vc-code>

}
fn main() {}