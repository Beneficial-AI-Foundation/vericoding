// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): predicate capturing that first n elements equal a given value */
spec fn all_equal_prefix(arr: &Vec<i32>, element: i32, n: int) -> bool { forall|i: int| 0 <= i < n ==> arr[i] == element }

/* helper modified by LLM (iteration 4): extend prefix equality by one when the next element matches */
proof fn all_equal_prefix_push(arr: &Vec<i32>, element: i32, n: int)
    requires
        0 <= n < arr.len() as int,
        all_equal_prefix(arr, element, n),
        arr[n] == element
    ensures
        all_equal_prefix(arr, element, n + 1)
{ }
// </vc-helpers>

// <vc-spec>
fn all_elements_equals(arr: &Vec<i32>, element: i32) -> (result: bool)

    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> (arr[i] == element)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): loop through all elements while maintaining a quantified invariant and provide a decreases clause */
    let mut i: usize = 0;
    let mut res: bool = true;

    while i < arr.len()
        invariant
            0 <= i as int <= arr.len() as int,
            res == (forall|j: int| 0 <= j < i as int ==> arr[j] == element)
        decreases (arr.len() - i) as int
    {
        res = res && (arr[i] == element);
        i += 1;
    }

    res
}
// </vc-code>

}
fn main() {}