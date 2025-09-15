// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The helper section has been intentionally left blank as there are no helper functions required for this task. */
// </vc-helpers>

// <vc-spec>
fn contains_consecutive_numbers(a: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| {
            &&& 0 <= i < a.len() - 1
            &&& #[trigger] a[i] + 1 == a[(i + 1) as int]
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatch errors by casting the array elements to `int` within the `forall` invariant to match the surrounding `int` context.*/
{
    let len = a.len();
    if len < 2 {
        return false;
    }

    let mut i: usize = 0;
    while i < len - 1
        invariant
            0 <= i as int && i as int <= len as int - 1,
            forall|j: int| 0 <= j < i ==> !(a[j as usize] as int + 1 == a[(j + 1) as usize] as int),
    {
        if a[i] + 1 == a[i + 1] {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}