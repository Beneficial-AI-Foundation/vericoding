// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert witness int index to usize */
proof fn find_finite_index(a: Vec<f32>) requires a.len() > 0, exists|i: int| 0 <= i && i < (a.len() as int) && is_finite(a[i as usize]) ensures exists|j: usize| j < a.len() && is_finite(a[j]) {
    proof {
        let k = choose(|k: int| 0 <= k && k < (a.len() as int) && is_finite(a[k as usize]));
        assert(0 <= k && k < (a.len() as int));
        let j: usize = k as usize;
        assert(j < a.len());
        assert(is_finite(a[j]));
    }
}
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
    /* code modified by LLM (iteration 5): find first finite element then track max index */
    let mut i: usize = 0;
    let mut idx: usize = 0;
    let mut found: bool = false;
    while i < a.len() {
        invariant (i as int) <= (a.len() as int);
        invariant (!found) ==> (forall|k: int| 0 <= k && k < (i as int) ==> !is_finite(a[k as usize]));
        invariant found ==> (0 <= (idx as int) && (idx as int) < (i as int) && is_finite(a[idx]));
        decreases a.len() - i;

        if !found {
            if is_finite(a[i]) {
                idx = i;
                found = true;
            }
        } else {
            if is_finite(a[i]) && a[i] > a[idx] {
                idx = i;
            }
        }
        i = i + 1;
    }
    proof {
        assert(i == a.len());
        let j = choose(|j: int| 0 <= j && j < (a.len() as int) && is_finite(a[j as usize]));
        if !found {
            assert(forall|k: int| 0 <= k && k < (i as int) ==> !is_finite(a[k as usize]));
            assert(!is_finite(a[j as usize]));
            assert(is_finite(a[j as usize]));
            assert(false);
        }
        assert(found);
        assert(is_finite(a[idx]));
    }
    idx
}
// </vc-code>

}
fn main() {}