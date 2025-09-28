// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fix type mismatches by casting lengths to int for Seq indexing and ranges */
proof fn lemma_seq_push_index_old<T>(s: Seq<T>, x: T, i: int)
    requires
        0 <= i < s.len() as int,
    ensures
        (s.push(x))[i] == s[i],
{}

/* helper modified by LLM (iteration 2): fix type mismatches by casting lengths to int for Seq indexing */
proof fn lemma_seq_push_index_new<T>(s: Seq<T>, x: T)
    ensures
        (s.push(x))[s.len() as int] == x,
{}

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
    /* code modified by LLM (iteration 2): switched to usize indices and used seq-view invariants for correctness */
    let mut result = Vec::<f32>::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i as int ==> result@[k] == a@[k],
        decreases (a.len() as int) - (i as int)
    {
        let ai = a[i];
        result.push(ai);
        i = i + 1;
    }
    let mut j: usize = 0;
    while j < b.len()
        invariant
            j <= b.len(),
            result.len() == a.len() + j,
            forall|k: int| 0 <= k < a.len() as int ==> result@[k] == a@[k],
            forall|k: int| 0 <= k < j as int ==> result@[(a.len() as int) + k] == b@[k],
        decreases (b.len() as int) - (j as int)
    {
        let bj = b[j];
        result.push(bj);
        j = j + 1;
    }
    result
}
// </vc-code>

}
fn main() {}