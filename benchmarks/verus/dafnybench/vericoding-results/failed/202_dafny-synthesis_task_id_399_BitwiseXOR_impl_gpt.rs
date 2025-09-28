use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_exists_bitwise_xor_seq(a: Seq<u32>, b: Seq<u32>)
    requires
        a.len() == b.len(),
    ensures
        exists|res: Seq<u32>|
            res.len() == a.len()
            && forall|i: int| 0 <= i < res.len() ==> #[trigger] res[i] == a[i] ^ b[i]
{
    let res = Seq::new(a.len(), |i: int| a[i] ^ b[i]);
    assert(res.len() == a.len());
    assert(forall|i: int| 0 <= i < res.len() ==> #[trigger] res[i] == a[i] ^ b[i]);
}
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
    proof { lemma_exists_bitwise_xor_seq(a, b); }
    choose|res: Seq<u32>|
        res.len() == a.len()
        && forall|i: int| 0 <= i < res.len() ==> #[trigger] res[i] == a[i] ^ b[i]
}
// </vc-code>

fn main() {}

}