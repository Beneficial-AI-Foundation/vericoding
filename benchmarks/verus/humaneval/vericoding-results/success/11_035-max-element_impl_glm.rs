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
/* code modified by LLM (iteration 4): fixed vector indexing syntax in invariant to use a@[j] instead of a@j> */
{
    let mut max = a[0];
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i as int <= a.len() as int,
            forall|j: int| 0 <= j < i as int ==> a@[j] <= max,
            exists|j: int| 0 <= j < i as int && a@[j] == max,
        decreases (a.len() as int) - (i as int)
    {
        if a[i] > max {
            max = a[i];
        }
        i += 1;
    }
    max
}
// </vc-code>

}
fn main() {}