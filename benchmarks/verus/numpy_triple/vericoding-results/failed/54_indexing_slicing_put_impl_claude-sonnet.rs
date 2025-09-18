// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn index_not_in_ind(j: int, ind: Vec<usize>) -> bool {
    forall|i: int| 0 <= i < ind.len() ==> j != ind[i]
}

proof fn lemma_unchanged_indices(a: Vec<f64>, ind: Vec<usize>, v: Vec<f64>, result: Vec<f64>, j: int)
    requires
        result.len() == a.len(),
        0 <= j < result.len(),
        index_not_in_ind(j, ind),
        forall|k: int| 0 <= k < result.len() ==> 
            (index_not_in_ind(k, ind) ==> result[k] == a[k]),
    ensures
        result[j] == a[j]
{
}

/* helper modified by LLM (iteration 5): fixed parameter type from int to usize */
proof fn lemma_bounds_check(ind: Vec<usize>, v: Vec<f64>, i: usize)
    requires
        ind.len() == v.len(),
        0 <= i < ind.len(),
    ensures
        0 <= i < v.len(),
        0 <= i < ind.len()
{
}

/* helper modified by LLM (iteration 5): added proof helper to preserve invariant during loop */
proof fn lemma_preservation(a: Vec<f64>, ind: Vec<usize>, v: Vec<f64>, result: Vec<f64>, old_result: Vec<f64>, i: usize)
    requires
        result.len() == a.len(),
        old_result.len() == a.len(),
        0 <= i < ind.len(),
        ind.len() == v.len(),
        forall|k: int| 0 <= k < ind.len() ==> ind[k] < a.len(),
        forall|k: int| 0 <= k < i ==> old_result[ind[k] as int] == v[k],
        forall|j: int| 0 <= j < old_result.len() ==> 
            (forall|k: int| 0 <= k < i ==> j != ind[k]) ==> old_result[j] == a[j],
        result == old_result.update(ind[i] as int, v[i as int]),
    ensures
        forall|k: int| 0 <= k < (i + 1) ==> result[ind[k] as int] == v[k],
        forall|j: int| 0 <= j < result.len() ==> 
            (forall|k: int| 0 <= k < (i + 1) ==> j != ind[k]) ==> result[j] == a[j]
{
}
// </vc-helpers>

// <vc-spec>
fn put(a: Vec<f64>, ind: Vec<usize>, v: Vec<f64>) -> (result: Vec<f64>)
    requires 
        ind.len() == v.len(),
        forall|i: int| 0 <= i < ind.len() ==> ind[i] < a.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < ind.len() ==> result[ind[i] as int] == v[i],
        forall|j: int| 0 <= j < result.len() ==> 
            (forall|i: int| 0 <= i < ind.len() ==> j != ind[i]) ==> result[j] == a[j],
        ind.len() == 0 ==> result@ == a@,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed invariant preservation with proof blocks */
    let mut result = a.clone();
    let mut i = 0;
    
    proof {
        assert(forall|j: int| 0 <= j < result.len() ==> 
            (forall|k: int| 0 <= k < 0 ==> j != ind[k]) ==> result[j] == a[j]);
    }
    
    while i < ind.len()
        invariant
            result.len() == a.len(),
            0 <= i <= ind.len(),
            ind.len() == v.len(),
            forall|k: int| 0 <= k < ind.len() ==> ind[k] < a.len(),
            forall|k: int| 0 <= k < i ==> result[ind[k] as int] == v[k],
            forall|j: int| 0 <= j < result.len() ==> 
                (forall|k: int| 0 <= k < i ==> j != ind[k]) ==> result[j] == a[j],
        decreases ind.len() - i
    {
        proof {
            lemma_bounds_check(ind, v, i);
        }
        let old_result = result;
        result.set(ind[i] as usize, v[i as usize]);
        
        proof {
            lemma_preservation(a, ind, v, result, old_result, i);
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}