// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_even_at_even_index(arr: &Vec<usize>) -> (result: bool)

    ensures
        result == forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2)),
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 4): Added decreases clause to the while loop to fix compilation error */
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len() as int,
            forall |j: int| 0 <= j < i ==> (j % 2 == (arr@[j] as int) % 2)
        decreases arr.len() - i
    {
        if i % 2 != arr[i] % 2 {
            return false;
        } else {
            proof {
                assert((i as int) % 2 == (arr@[i as int] as int) % 2);
            }
        }
        i += 1;
    }
    return true;
}
// </vc-code>

}
fn main() {}