// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_index_concat_prefix<T>(s1: Seq<T>, s2: Seq<T>, i: int)
    requires
        0 <= i < s1.len(),
    ensures
        (s1 + s2)[i] == s1[i]
{ }

proof fn lemma_index_concat_suffix<T>(s1: Seq<T>, s2: Seq<T>, j: int)
    requires
        0 <= j < s2.len(),
    ensures
        (s1 + s2)[s1.len() + j] == s2[j]
{ }
// </vc-helpers>

// <vc-spec>
fn concatenate(a: Vec<f32>, b: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == a.len() + b.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
        forall|j: int| 0 <= j < b.len() ==> result[a.len() + j] == b[j],
// </vc-spec>
// <vc-code>
{
    let mut result = a;
    let mut bb = b;
    result.append(&mut bb);
    result
}
// </vc-code>

}
fn main() {}