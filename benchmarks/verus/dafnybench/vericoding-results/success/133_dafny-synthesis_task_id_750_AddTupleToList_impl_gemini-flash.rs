use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
proof fn add_tuple_to_list(l: Seq<(int, int)>, t: (int, int)) -> (r: Seq<(int, int)>)
    ensures
        r.len() == l.len() + 1,
        r[r.len() - 1] == t,
        forall|i: int| 0 <= i < l.len() ==> r[i] == l[i]
// </vc-spec>
// <vc-code>
{
    let l_len = l.len();
    assert(l_len >= 0);
    let r = l.push(t);

    // No need for a separate proof block here, as auto-inferred postconditions
    // and simple assertions directly follow from `Seq::push`'s properties.
    // The `assert forall` can be inlined or relied upon by the verifier for simple cases.

    // The Verus verifier can often infer these properties from the definition of `Seq::push`.
    // Explicit assertions without a proof block are usually sufficient for direct consequences.
    assert(r.len() == l_len + 1);
    assert(r.last() == t); // `r[r.len() - 1]` is equivalent to `r.last()`

    // For the `forall` condition, Verus's native understanding of `Seq::push`
    // is often sufficient. If not, an `assert forall` without a `proof` block
    // often works in a method's body.
    assert forall |i: int| 0 <= i < l.len() implies r[i] == l[i] by {
        // This holds directly from the definition of Seq::push,
        // which appends an element without modifying existing ones.
        // No complex steps are needed for `by` clause.
    }
    r
}
// </vc-code>

fn main() {
}

} // verus!