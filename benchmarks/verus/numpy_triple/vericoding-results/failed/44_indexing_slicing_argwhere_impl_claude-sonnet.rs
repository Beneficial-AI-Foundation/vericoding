// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): strengthened lemma to prove distinctness from sortedness */
proof fn lemma_sorted_indices(indices: &Vec<usize>, i: usize, j: usize)
    requires
        i < indices.len(),
        j < indices.len(),
        i != j,
        forall|x: int, y: int| 0 <= x < indices.len() && 0 <= y < indices.len() && (indices[x] as int) < (indices[y] as int) ==> x < y
    ensures
        indices[i as int] != indices[j as int]
{
    proof {
        if i < j {
            assert(indices[i as int] < indices[j as int]);
        } else {
            assert(j < i);
            assert(indices[j as int] < indices[i as int]);
        }
    }
}

proof fn lemma_indices_properties(a: &Vec<f64>, indices: &Vec<usize>, i: usize)
    requires
        i < indices.len(),
        forall|k: int| 0 <= k < indices.len() ==> indices[k] < a.len(),
        forall|k: int| 0 <= k < indices.len() ==> a[indices[k] as int] != 0.0
    ensures
        indices[i as int] < a.len(),
        a[indices[i as int] as int] != 0.0
{
}
// </vc-helpers>

// <vc-spec>
fn argwhere(a: &Vec<f64>) -> (indices: Vec<usize>)
    ensures
        forall|i: int| 0 <= i < indices.len() ==> (#[trigger] indices[i]) < a.len(),
        forall|i: int| 0 <= i < indices.len() ==> a[indices[i] as int] != 0.0,
        forall|i: int| 0 <= i < a.len() && a[i] != 0.0 ==> exists|j: int| 0 <= j < indices.len() && indices[j] == i,
        forall|i: int, j: int| 0 <= i < indices.len() && 0 <= j < indices.len() && i != j ==> indices[i] != indices[j],
        forall|i: int, j: int| 0 <= i < indices.len() && 0 <= j < indices.len() && (indices[i] as int) < (indices[j] as int) ==> i < j,
        (indices.len() == 0) == (forall|i: int| 0 <= i < a.len() ==> a[i] == 0.0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatch by using int indexing */
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < indices.len() ==> (#[trigger] indices[k]) < a.len(),
            forall|k: int| 0 <= k < indices.len() ==> a[#[trigger] indices[k] as int] != 0.0,
            forall|k: int| 0 <= k < a.len() && k < i && a[k] != 0.0 ==> exists|j: int| 0 <= j < indices.len() && indices[j] == k,
            forall|k: int, j: int| 0 <= k < indices.len() && 0 <= j < indices.len() && k != j ==> indices[k] != indices[j],
            forall|k: int, j: int| 0 <= k < indices.len() && 0 <= j < indices.len() && (indices[k] as int) < (indices[j] as int) ==> k < j
        decreases a.len() - i
    {
        if a[i as int] != 0.0 {
            proof {
                assert(i < a.len());
                assert(a[i as int] != 0.0);
                assert(forall|k: int| 0 <= k < indices.len() ==> indices[k] < i);
            }
            indices.push(i);
        }
        i += 1;
    }
    
    proof {
        assert(i == a.len());
        assert(forall|k: int| 0 <= k < a.len() && a[k] != 0.0 ==> exists|j: int| 0 <= j < indices.len() && indices[j] == k);
        if indices.len() == 0 {
            assert(forall|k: int| 0 <= k < a.len() ==> a[k] == 0.0);
        } else {
            assert(exists|k: int| 0 <= k < a.len() && a[k] != 0.0);
        }
    }
    
    indices
}
// </vc-code>

}
fn main() {}