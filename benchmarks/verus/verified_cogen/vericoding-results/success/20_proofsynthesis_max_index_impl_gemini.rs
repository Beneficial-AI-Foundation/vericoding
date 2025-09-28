// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun1(x: &Vec<i32>) -> (max_index: usize)

    requires
        x.len() >= 1,

    ensures
        forall|k: int| 0 <= k < x.len() ==> x[max_index as int] >= x[k],
        max_index < x.len(),
// </vc-spec>
// <vc-code>
{
    let mut max_index: usize = 0;
    let mut i: usize = 1;
    while i < x.len()
        invariant
            x.len() >= 1,
            1 <= i <= x.len(),
            max_index < i,
            forall|k: int| 0 <= k < (i as int) ==> x@[(max_index as int)] >= x@[k],
        decreases x.len() - i
    {
        if x[i] > x[max_index] {
            max_index = i;
        }
        i = i + 1;
    }
    max_index
}
// </vc-code>

}
fn main() {}