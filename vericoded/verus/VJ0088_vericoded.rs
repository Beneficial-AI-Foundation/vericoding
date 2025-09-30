// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): predicate for all elements less than number */
spec fn all_less(arr: &Vec<i32>, number: i32) -> bool { forall|i: int| 0 <= i < arr.len() ==> number > arr[i] }
// </vc-helpers>

// <vc-spec>
fn is_greater(arr: &Vec<i32>, number: i32) -> (result: bool)

    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> number > arr[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): loop with invariant linking ok to prefix property */
    let mut i: usize = 0;
    let mut ok: bool = true;
    while i < arr.len()
        invariant
            i <= arr.len(),
            ok == (forall|j: int| 0 <= j < i as int ==> number > arr[j]),
        decreases arr.len() - i
    {
        if number > arr[i] {
            i = i + 1;
        } else {
            ok = false;
            i = arr.len();
        }
    }
    ok
}
// </vc-code>

}
fn main() {}