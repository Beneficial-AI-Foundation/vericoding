// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn index_in_bounds_lemma(ind: Seq<usize>, i: int, a_len: int) 
    requires 
        0 <= i < ind.len(),
        forall|k: int| 0 <= k < ind.len() ==> ind[k] < a_len
    ensures 
        ind[i] < a_len
{
    assert(ind[i] < a_len);
}

proof fn v_index_in_bounds_lemma(v: Seq<f64>, i: int) 
    requires 
        0 <= i < v.len()
    ensures 
        i < v.len()
{
    assert(i < v.len());
}

proof fn put_helper_lemma(a: Seq<f64>, ind: Seq<usize>, v: Seq<f64>, result: Seq<f64>) 
    requires 
        ind.len() == v.len(),
        forall|i: int| 0 <= i < ind.len() ==> ind[i] < a.len(),
        result.len() == a.len(),
        forall|i: int| 0 <= i < ind.len() ==> result[ind[i] as int] == v[i],
        forall|j: int| 0 <= j < result.len() ==> 
            (forall|i: int| 0 <= i < ind.len() ==> j != ind[i]) ==> result[j] == a[j]
    ensures 
        ind.len() == 0 ==> result == a
{
    if ind.len() == 0 {
        assert(result == a);
    }
}

proof fn trigger_helper(k: int, ind: Seq<usize>) -> bool {
    requires true;
    ensures result == (k < ind.len());
    k < ind.len()
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
    /* code modified by LLM (iteration 5): Add explicit trigger annotation to fix quantifier error */
    let mut result = a.clone();
    let mut i: usize = 0;
    
    while i < ind.len() 
        invariant 
            i <= ind.len(),
            result.len() == a.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] (k < ind.len()) && #[trigger] result[ind[k] as int] == v[k],
            forall|j: int| 0 <= j < result.len() ==> 
                (forall|k: int| 0 <= k < i ==> #[trigger] (j != ind[k])) ==> result[j] == a[j]
        decreases ind.len() - i
    {
        proof {
            v_index_in_bounds_lemma(v@, i as int);
            index_in_bounds_lemma(ind@, i as int, a.len() as int);
        }
        let index = ind[i];
        result[index] = v[i];
        
        proof {
            // Update invariants for next iteration with explicit triggers
            assert(forall|k: int| 0 <= k < i + 1 ==> #[trigger] trigger_helper(k, ind@) by {
                if 0 <= k < i + 1 {
                    assert(trigger_helper(k, ind@) == (k < ind.len()));
                }
            });
            assert(forall|k: int| 0 <= k < i + 1 ==> #[trigger] result[ind[k] as int] == v[k] by {
                if 0 <= k < i + 1 {
                    assert(result[ind[k] as int] == v[k]);
                }
            });
            assert(forall|j: int| 0 <= j < result.len() ==> 
                (forall|k: int| 0 <= k < i + 1 ==> #[trigger] (j != ind[k])) ==> result[j] == a[j] by {
                if 0 <= j < result.len() {
                    if forall|k: int| 0 <= k < i + 1 ==> j != ind[k] {
                        assert(result[j] == a[j]);
                    }
                }
            });
        }
        
        i += 1;
    }
    proof {
        put_helper_lemma(a@, ind@, v@, result@);
    }
    result
}
// </vc-code>

}
fn main() {}