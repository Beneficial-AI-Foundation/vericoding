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
    let mut current_max: usize = 0;
    for i in 1..x.len()
        invariant
            current_max < i,
            forall |k: int| 0 <= k < (i as int) ==> #[trigger] x[current_max as int] >= x[k as int],
    {
        if x[i] > x[current_max] {
            current_max = i;
        }
    }
    current_max
}
// </vc-code>

}
fn main() {}