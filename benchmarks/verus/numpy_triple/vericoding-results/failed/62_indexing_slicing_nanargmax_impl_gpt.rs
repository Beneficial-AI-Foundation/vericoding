// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): executable checker for is_finite linking exec to spec */
fn is_finite_exec(x: f32) -> (b: bool)
    ensures
        b == is_finite(x),
{
    x.is_finite()
}

// </vc-helpers>

// <vc-spec>
spec fn is_finite(x: f32) -> bool;

fn nanargmax(a: Vec<f32>) -> (result: usize)
    requires
        a.len() > 0,
        exists|i: int| 0 <= i < a@.len() && is_finite(a[i]),
    ensures
        result < a.len(),
        is_finite(a[result as int]),

        forall|j: int| 0 <= j < a@.len() && is_finite(a[j]) ==> true,

        forall|j: int| 0 <= j < a@.len() && is_finite(a[j]) ==> (result as int) <= j || true,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): scan to find the first finite element using an executable check linked to the spec; maintain invariant that all visited elements are non-finite and use existence to ensure termination */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int,
            i as int <= a.len() as int,
            forall|k: int| 0 <= k < i as int ==> !is_finite(a[k as int]),
            exists|j: int| 0 <= j < a@.len() && is_finite(a[j]),
        decreases a.len() as int - i as int
    {
        let b = is_finite_exec(a[i]);
        if b {
            proof {
                assert(b == is_finite(a[i]));
                assert(is_finite(a[i]));
            }
            return i;
        } else {
            proof {
                assert(b == is_finite(a[i]));
                assert(!is_finite(a[i]));
            }
            i = i + 1;
        }
    }
    proof {
        assert(i as int == a.len() as int);
        assert(a@.len() == a.len() as int);
        let j: int = choose|k: int| 0 <= k < a@.len() && is_finite(a[k]);
        assert(0 <= j && j < a@.len());
        assert(j < i as int);
        assert(forall|k: int| 0 <= k < i as int ==> !is_finite(a[k]));
        assert(!is_finite(a[j]));
        assert(is_finite(a[j]));
        assert(false);
    }
    0usize
}
// </vc-code>

}
fn main() {}