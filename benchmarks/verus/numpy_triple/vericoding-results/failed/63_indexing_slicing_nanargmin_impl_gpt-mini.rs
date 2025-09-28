// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn f32_is_nan(x: f32) -> bool;
spec fn f32_le(a: f32, b: f32) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert usize indices in specs to int-indexing */
proof fn exists_non_nan_implies_not_all_nan(a: Vec<f32>)
    requires
        a.len() > 0,
        exists|i: int| 0 <= i && i < a.len() as int && !f32_is_nan(a[i]),
    ensures
        !(forall|i: int| 0 <= i && i < a.len() as int ==> f32_is_nan(a[i])),
{
    proof {
        let j: int = choose |j: int| 0 <= j && j < a.len() as int && !f32_is_nan(a[j]);
        assert(!f32_is_nan(a[j]));
        assert(!(forall|i: int| 0 <= i && i < a.len() as int ==> f32_is_nan(a[i])));
    }
}

// </vc-helpers>

// <vc-spec>
fn nanargmin(a: Vec<f32>) -> (result: usize)
    requires 
        a.len() > 0,
        exists|i: int| 0 <= i < a.len() && !f32_is_nan(a[i]),
    ensures
        result < a.len(),
        !f32_is_nan(a[result as int]),
        forall|j: int| 0 <= j < a.len() && !f32_is_nan(a[j]) ==> f32_le(a[result as int], a[j]),
        forall|j: int| 0 <= j < a.len() && !f32_is_nan(a[j]) && f32_le(a[j], a[result as int]) && f32_le(a[result as int], a[j]) ==> result as int <= j,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix spec indexing to use int indices and cast best when used in specs */
    let mut i: usize = 0usize;

    // find first non-NaN index
    while i < a.len() && f32_is_nan(a[i])
        invariant
            i <= a.len(),
            forall|k: int| 0 <= k && k < i as int ==> f32_is_nan(a[k]),
        decreases a.len() - i
    {
        i += 1;
    }

    proof {
        let j: int = choose |j: int| 0 <= j && j < a.len() as int && !f32_is_nan(a[j]);
        assert(forall|k: int| 0 <= k && k < i as int ==> f32_is_nan(a[k]));
        assert(i < a.len());
        assert(!f32_is_nan(a[i]));
    }

    let mut best: usize = i;
    i += 1;

    // scan remaining elements, keeping best as index of minimal non-NaN seen so far
    while i < a.len()
        invariant
            i <= a.len(),
            best < a.len(),
            !f32_is_nan(a[best as int]),
            forall|k: int| 0 <= k && k < i as int && !f32_is_nan(a[k]) ==> f32_le(a[best as int], a[k]),
            forall|k: int| 0 <= k && k < i as int && !f32_is_nan(a[k]) && f32_le(a[k], a[best as int]) && f32_le(a[best as int], a[k]) ==> best as int <= k,
        decreases a.len() - i
    {
        if !f32_is_nan(a[i]) {
            // prefer strictly smaller values; on equality keep earlier index (do not update)
            if f32_le(a[i], a[best]) && !f32_le(a[best], a[i]) {
                best = i;
            }
        }
        i += 1;
    }

    proof {
        // establish ensures in terms of int-indexed specifications by casting
        assert(best < a.len());
        assert(!f32_is_nan(a[best as int]));
        assert(forall|j: int|
            0 <= j && j < a.len() as int && !f32_is_nan(a[j]) ==>
                f32_le(a[best as int], a[j])
        );
        assert(forall|j: int|
            0 <= j && j < a.len() as int && !f32_is_nan(a[j]) && f32_le(a[j], a[best as int]) && f32_le(a[best as int], a[j]) ==>
                (best as int) <= j
        );
    }

    best
}

// </vc-code>

}
fn main() {}