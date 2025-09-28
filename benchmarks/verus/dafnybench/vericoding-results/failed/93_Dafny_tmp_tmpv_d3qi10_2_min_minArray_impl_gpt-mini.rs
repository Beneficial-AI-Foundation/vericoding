use vstd::prelude::*;

verus! {

spec fn min(a: int, b: int) -> int 
{
    if a < b { a } else { b }
}

spec fn min_function(a: int, b: int) -> int 
{
    if a < b { a } else { b }
}

// <vc-helpers>
// <vc-helpers>
// Helper lemmas for relating Vec indexing with `@`-style indexing.
// These are small, straightforward facts used in the post-proof.
proof fn vec_index_equiv<T: Copy + PartialEq>(a: &Vec<T>, i: usize)
    requires i < a.len()
    ensures a@[i as int] == a[i]
{
    // This follows from the semantic definition of `@` indexing;
    // Verus can check this directly given the bound on i.
    assert(a@[i as int] == a[i]);
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min_array(a: &Vec<i32>) -> (m: i32)
    requires a.len() > 0
    ensures forall|k: int| 0 <= k < a.len() ==> m <= a[k]
    ensures exists|k: int| 0 <= k < a.len() && m == a[k]
// </vc-spec>
// <vc-code>
{
    // Initialize with first element (safe because a.len() > 0)
    let mut i: usize = 1;
    let mut min_idx: usize = 0;
    let mut m: i32 = a[0];

    // Loop over remaining elements, maintaining that `m` is the minimum
    // of the prefix a[0..i).
    while i < a.len()
        invariant i <= a.len()
        invariant min_idx < i
        invariant m == a[min_idx]
        invariant forall |k: int| 0 <= k && k < (i as int) ==> (m as int) <= (a@[k] as int)
    {
        let v: i32 = a[i];
        if v < m {
            // update m and the index of the minimum to the new smaller value
            m = v;
            min_idx = i;
        }
        i += 1;
    }

    // Prove postconditions: (1) m is <= every element; (2) m equals some element.
    proof {
        // From loop exit we have i >= a.len(). Together with invariant i <= a.len(),
        // conclude i == a.len().
        assert(i == a.len());

        // Use the quantified invariant with i == a.len() to get the full-range bound.
        assert(forall |k: int| 0 <= k && k < (i as int) ==> (m as int) <= (a@[k] as int));
        assert(forall |k: int| 0 <= k && k < (a.len() as int) ==> (m as int) <= (a@[k] as int));

        // Show existence: witness is min_idx.
        let k: int = min_idx as int;
        // min_idx < a.len() follows from min_idx < i and i == a.len()
        assert(min_idx < a.len());
        assert(0 <= k);
        assert(k < (a.len() as int));

        // m == a[min_idx] is an invariant; relate the integer-indexed view a@[k] to a[min_idx].
        assert(m == a[min_idx]);
        vec_index_equiv(a, min_idx);
        assert(a@[k] == a[min_idx]);

        // Conclude m equals a@[k].
        assert(m == a@[k]);
    }

    m
}
// </vc-code>

fn main() {
}

}