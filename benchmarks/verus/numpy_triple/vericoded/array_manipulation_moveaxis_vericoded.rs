// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_seq_pointwise_equal_implies_equal<T>(a: Seq<T>, b: Seq<T>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] == b[i],
    ensures
        a == b,
{
}

pub open spec fn identity_seq<T>(s: Seq<T>) -> Seq<T> {
    s
}
// </vc-helpers>

// <vc-spec>
fn moveaxis(a: Vec<f32>, source: usize, dest: usize) -> (result: Vec<f32>)
    ensures
        /* Core property: moveaxis on 1D array is identity */
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
        /* Sanity check: size is preserved */
        result.len() == a.len(),
        /* Mathematical property: for 1D arrays, result equals input */
        result@ == a@,
// </vc-spec>
// <vc-code>
{
    a
}
// </vc-code>


}
fn main() {}