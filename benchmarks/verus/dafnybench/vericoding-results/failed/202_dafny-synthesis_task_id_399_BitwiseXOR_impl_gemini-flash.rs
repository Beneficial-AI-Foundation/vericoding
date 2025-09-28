use vstd::prelude::*;

verus! {

// <vc-helpers>
fn seq_bitwise_xor(a: &Seq<u32>, b: &Seq<u32>) -> (bitxor_result: Seq<u32>)
    requires
        a.len() == b.len(),
    ensures
        bitxor_result.len() == a.len(),
        forall|i: int| #![trigger bitxor_result[i]] 0 <= i < bitxor_result.len() ==> bitxor_result[i] == a[i] ^ b[i],
{
    let mut result = Seq::<u32>::new();
    let mut i: int = 0;

    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| #![trigger result[j]] 0 <= j < i ==> result[j] == a[j] ^ b[j],
    {
        result = result.push(a[i] ^ b[i]);
        i = i + 1;
    }
    result
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
    let mut result: Vec<u32> = Vec::new();
    let mut i: u64 = 0; // Changed to a concrete integer type

    while (i as int) < a.len()
        invariant
            0 <= i as int <= a.len(),
            (result.len() as int) == i as int,
            forall|j: int| #![trigger result.view_nth(j)] 0 <= j < i as int ==> result.view_nth(j) == a[j] ^ b[j],
    {
        result.push(a[i as int] ^ b[i as int]); // Use direct indexing for Seq
        i = i + 1;
    }

    proof {
        assert(result.len() == a.len());
        assert(forall|k: int| 0 <= k < result.len() ==> result.view_nth(k) == a[k] ^ b[k]);
    }

    result.to_seq()
}
// </vc-code>

fn main() {}

}