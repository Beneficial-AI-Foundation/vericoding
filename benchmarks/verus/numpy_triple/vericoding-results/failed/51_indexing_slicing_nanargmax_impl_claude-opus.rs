// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn is_finite(x: f32) -> bool;

fn nanargmax(a: Vec<f32>) -> (result: usize)
    requires
        a.len() > 0,
        exists|i: int| 0 <= i < a.len() && is_finite(a[i]),
    ensures
        result < a.len(),
        is_finite(a[result as int]),

        forall|j: int| 0 <= j < a.len() && is_finite(a[j]) ==> true,

        forall|j: int| 0 <= j < a.len() && is_finite(a[j]) ==> (result as int) <= j || true,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed loop invariants and logic */
    let mut max_idx: usize = 0;
    let mut found_finite = false;
    
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            !found_finite ==> forall|j: int| 0 <= j < i ==> !is_finite(a[j]),
            found_finite ==> max_idx < a.len(),
            found_finite ==> is_finite(a[max_idx as int]),
            found_finite ==> max_idx < i,
        decreases a.len() - i
    {
        if a[i] == a[i] {  // Check if not NaN
            if !found_finite {
                max_idx = i;
                found_finite = true;
                assert(is_finite(a[max_idx as int]));
            } else if a[i] > a[max_idx] {
                max_idx = i;
                assert(is_finite(a[max_idx as int]));
            }
        }
        i = i + 1;
    }
    
    assert(found_finite) by {
        assert(exists|j: int| 0 <= j < a.len() && is_finite(a[j]));
        if !found_finite {
            assert(forall|j: int| 0 <= j < a.len() ==> !is_finite(a[j]));
            assert(false);
        }
    }
    
    max_idx
}
// </vc-code>

}
fn main() {}