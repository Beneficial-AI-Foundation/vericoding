use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers; the fixes are in the code and adjusted in the spec implicitly via output format, but per requirements,Preserve SPEC.
// </vc-helpers>

// <vc-spec>
fn bitwise_xor(a: Seq<u32>, b: Seq<u32>) -> (result: Seq<u32>)
    requires
        a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] ^ b[i],
// </vc-spec>
// <vc-code>
{
    let mut i = 0nat;
    let mut result_vec = seq![]);
    while i < a.len()
        invariant
            a.len() == b.len(),
            result_vec.len() == i,
            forall|j: nat| 0 <= j < i ==> #[trigger] result_vec[j] == a[j] ^ b[j]
    {
        result_vec = result_vec.add(a[i] ^ b[i]);
        i = add(1);
    }
    result_vec
}
// </vc-code>

fn main() {}

}