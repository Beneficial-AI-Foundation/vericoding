// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed predicate syntax and added helper lemmas */
predicate!{
    is_nonzero_index(i: int, a: Seq<f32>) -> bool {
        0 <= i < a.len() && a[i] != 0.0f32
    }
}

predicate!{
    indices_sorted(indices: Seq<int>) -> bool {
        forall|i1: int, i2: int| 0 <= i1 < i2 < indices.len() ==> indices[i1] < indices[i2]
    }
}

predicate!{
    indices_unique(indices: Seq<int>) -> bool {
        forall|i: int, j: int| 0 <= i < j < indices.len() ==> indices[i] != indices[j]
    }
}

lemma nonnegative_decreases(n: nat) 
    decreases n
{
    if n > 0 {
        nonnegative_decreases(n - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn nonzero(a: Vec<f32>) -> (indices: Vec<usize>)
    ensures
        forall|i: int| 0 <= i < indices.len() ==> (indices[i] < a.len() && a[indices[i] as int] != 0.0f32),
        forall|j: int| 0 <= j < a.len() ==> (a[j] != 0.0f32 <==> exists|k: int| 0 <= k < indices.len() && indices[k] == j),
        forall|i1: int, i2: int| 0 <= i1 < i2 < indices.len() ==> indices[i1] < indices[i2],
        forall|i: int, j: int| 0 <= i < j < indices.len() ==> indices[i] != indices[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed loop invariant and added proper index handling */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            result.len() <= i,
            forall|k: int| 0 <= k < result.len() ==> (result[k] < a.len() && a[result[k] as int] != 0.0f32),
            forall|j: int| 0 <= j < i ==> (a[j] != 0.0f32 <==> exists|k: int| 0 <= k < result.len() && result[k] == j as usize),
            indices_sorted(result@),
            indices_unique(result@),
        decreases a.len() - i
    {
        if a[i as int] != 0.0f32 {
            result.push(i);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}