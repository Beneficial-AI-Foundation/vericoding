// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn max_element(a: &Vec<i32>) -> (max: i32)

    requires
        a.len() > 0,

    ensures
        forall|i: int| 0 <= i < a.len() ==> a[i] <= max,
        exists|i: int| 0 <= i < a.len() && a[i] == max,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed type mismatch by using a.len() instead of a@.len() in while condition */
    let mut max_val: i32 = a[0];
    let mut index: usize = 1;
    while index < a.len()
        invariant
            0 <= index as int && index <= a@.len(),
            forall|k: int| 0 <= k < index as int ==> a@[k] <= max_val,
            exists|k: int| 0 <= k < index as int && a@[k] == max_val,
        decreases a@.len() - index as int
    {
        if a[index] > max_val {
            max_val = a[index];
        }
        index += 1;
    }
    max_val
}
// </vc-code>

}
fn main() {}