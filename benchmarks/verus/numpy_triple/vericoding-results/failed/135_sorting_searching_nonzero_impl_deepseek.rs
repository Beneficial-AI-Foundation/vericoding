// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

fn is_nonzero_f32(x: f32) -> bool {
    x != 0.0f32
}

spec fn seq_nonzero_indices(s: Seq<f32>) -> Seq<nat>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        let sub_seq = seq_nonzero_indices(s.subrange(0, s.len() - 1));
        if s[s.len() - 1] != 0.0f32 {
            sub_seq.push(s.len() - 1)
        } else {
            sub_seq
        }
    }
}

proof fn seq_nonzero_indices_valid(s: Seq<f32>, k: int)
    requires
        0 <= k < s.len(),
    ensures
        s[k] != 0.0f32 <==> exists|i: int| 0 <= i < seq_nonzero_indices(s).len() && seq_nonzero_indices(s)[i] == k
{
}

proof fn seq_nonzero_indices_sorted(s: Seq<f32>)
    ensures
        forall|i1: int, i2: int| 0 <= i1 < i2 < seq_nonzero_indices(s).len() ==> seq_nonzero_indices(s)[i1] < seq_nonzero_indices(s)[i2]
{
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
{
    let mut indices = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            indices.len() == seq_nonzero_indices(a@.subrange(0, i as int)).len(),
            forall|k: int| 0 <= k < indices.len() ==> indices[k] < i,
            forall|k: int| 0 <= k < indices.len() ==> a[indices[k]] != 0.0f32,
            forall|j: int| 0 <= j < i ==> (a[j] != 0.0f32 <==> exists|k: int| 0 <= k < indices.len() && indices[k] == j as usize),
            forall|k1: int, k2: int| 0 <= k1 < k2 < indices.len() ==> indices[k1] < indices[k2],
    {
        if is_nonzero_f32(a[i]) {
            indices.push(i);
        }
        i += 1;
    }
    indices
}
// </vc-code>

}
fn main() {}