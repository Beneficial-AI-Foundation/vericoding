// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed type errors by using a usize loop counter and .index() for Seq access. */
    let mut result_vec = Vec::<u32>::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == b.len(),
            result_vec.view().len() == i as nat,
            forall|j: int| 0 <= j < i as int ==> result_vec.view()@[j] == a@[j] ^ b@[j],
    {
        let xor_val = *a.index(i as int) ^ *b.index(i as int);
        result_vec.push(xor_val);
        i = i + 1;
    }
    result_vec.view()
}
// </vc-code>

}
fn main() {}