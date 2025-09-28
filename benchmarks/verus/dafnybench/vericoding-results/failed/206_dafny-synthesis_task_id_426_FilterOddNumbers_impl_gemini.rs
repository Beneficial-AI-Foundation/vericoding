// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed the `is_odd_exec` helper, as the function operates on ghost type `int` and does not need an executable helper using `i64`. */
// </vc-helpers>

// <vc-spec>
fn filter_odd_numbers(arr: &[int]) -> (odd_list: Vec<int>)
    ensures 

        forall|i: int| 0 <= i < odd_list.len() ==> is_odd(odd_list[i]) && arr@.contains(odd_list[i]),

        forall|i: int| 0 <= i < arr.len() && is_odd(arr[i]) ==> odd_list@.contains(arr[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Re-implemented using a ghost while-loop and sequences (Seq) to fix compilation errors and correctly handle the ghost nature of the function signature (&[int]). */
    let mut odd_list_ghost: Seq<int> = Seq::empty();
    let mut i: int = 0;

    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < odd_list_ghost.len() ==> is_odd(odd_list_ghost@[j]),
            forall|x: int| odd_list_ghost.contains(x) ==> arr@.subrange(0, i).contains(x),
            forall|k: int| 0 <= k < i && is_odd(arr@[k]) ==> odd_list_ghost.contains(arr@[k]),
        decreases arr.len() - i
    {
        let x = arr@[i];
        if is_odd(x) {
            odd_list_ghost = odd_list_ghost.push(x);
        }
        i = i + 1;
    }

    let odd_list = Vec { vec: odd_list_ghost };
    odd_list
}
// </vc-code>

}
fn main() {}