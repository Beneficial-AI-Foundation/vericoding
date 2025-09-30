// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial arithmetic proof */
proof fn trivial_proof() {
    assert(1 + 1 == 2);
}

// </vc-helpers>

// <vc-spec>
fn has_only_one_distinct_element(a: &Vec<i32>) -> (result: bool)
    requires a.len() > 0,
    ensures
        result ==> (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j]),
        !result ==> (exists|i: int| 0 <= i < a.len() && #[trigger] a[i] != a[0]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate over vector and check all elements equal to the first */
    let mut i: usize = 1;
    while i < a.len()
        invariant
            forall|k: int| 0 <= k && k < i as int ==> #[trigger] a[k] == a[0],
        decreases (a.len() as int) - (i as int)
    {
        if a[i] != a[0] {
            return false;
        }
        i += 1;
    }
    true
}

// </vc-code>

}
fn main() {}