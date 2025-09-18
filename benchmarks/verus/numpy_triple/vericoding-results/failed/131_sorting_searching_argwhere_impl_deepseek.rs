// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed sorted_indices parameter type */
    spec fn is_nonzero(a: f64) -> bool {
        a != 0.0
    }

    spec fn valid_indices(a: Seq<f64>, indices: Seq<usize>) -> bool {
        forall|i: int| 0 <= i < indices.len() ==> indices[i] < a.len() && is_nonzero(a[indices[i] as int])
    }

    spec fn complete_indices(a: Seq<f64>, indices: Seq<usize>) -> bool {
        forall|i: int| 0 <= i < a.len() && is_nonzero(a[i]) ==> indices.contains(i as usize)
    }

    spec fn distinct_indices(indices: Seq<usize>) -> bool {
        forall|i: int, j: int| 0 <= i < j < indices.len() ==> indices[i] != indices[j]
    }

    spec fn sorted_indices(indices: Seq<usize>) -> bool {
        forall|i: int, j: int| 0 <= i < j < indices.len() ==> indices[i] < indices[j]
    }

    proof fn lemma_index_ordering_maintains_distinctness()
        ensures
            forall|s: Seq<usize>| sorted_indices(s) ==> distinct_indices(s)
    {
        assert forall|s: Seq<usize>| sorted_indices(s) implies distinct_indices(s) by {
            assert forall|i: int, j: int| 0 <= i < j < s.len() implies s[i] != s[j] by {
                if s[i] == s[j] {
                    assert(s[i] < s[j]) by {
                        assert(sorted_indices(s));
                    };
                    assert(false);
                }
            }
        }
    }

    proof fn lemma_push_maintains_sorted_order(indices: Seq<usize>, new_index: usize)
        requires
            sorted_indices(indices),
            indices.len() == 0 || indices[indices.len() as int - 1] < new_index
        ensures
            sorted_indices(indices.push(new_index))
    {
    }
// </vc-helpers>

// <vc-spec>
fn numpy_argwhere(a: Vec<f64>) -> (indices: Vec<usize>)
    ensures

        forall|i: int| 0 <= i < indices.len() ==> 
            indices[i] < a.len() && a[indices[i] as int] != 0.0,

        forall|i: int| 0 <= i < a.len() && a[i] != 0.0 ==> 
            indices@.contains(i as usize),

        forall|i: int, j: int| 0 <= i < j < indices.len() ==> 
            indices[i] != indices[j],

        forall|i: int, j: int| 0 <= i < j < indices.len() ==> 
            indices[i] < indices[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed sorted_indices parameter passing */
{
    let mut indices = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            valid_indices(a@, indices@),
            sorted_indices(indices@),
            forall|k: int| 0 <= k < i && a@[k] != 0.0 ==> indices@.contains(k as usize)
        decreases a.len() - i
    {
        if a[i] != 0.0 {
            proof {
                lemma_push_maintains_sorted_order(indices@, i);
            }
            indices.push(i);
        }
        i += 1;
    }
    
    proof {
        lemma_index_ordering_maintains_distinctness();
    }
    
    indices
}
// </vc-code>

}
fn main() {}