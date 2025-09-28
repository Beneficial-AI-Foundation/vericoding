// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fix type mismatches and indexing */
fn filter_even_indices(seq: Seq<i8>) -> Seq<i8>
    decreases seq.len(),
{
    if seq.len() == 0 {
        Seq::empty()
    } else {
        let rest_len = seq.len() - 1;
        let filtered_rest = filter_even_indices(seq.subrange(1, rest_len as int));
        if 0 % 2 == 0 {
            Seq::new(seq.len() / 2 + 1, |i: int| if i == 0 { seq@[0] } else { filtered_rest@[i-1] })
        } else {
            filtered_rest
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn sorted_even(a: Vec<i8>) -> (sorted: Vec<i8>)
    requires 
        a@.len() > 0
    ensures 
        sorted@.len() == a@.len(),
        forall|i: int, j: int| 0 <= i < j && 2 * i < sorted@.len() && 2 * j < sorted@.len() ==> #[trigger] sorted@[2 * i] <= #[trigger] sorted@[2 * j],
        forall|i: int| 0 <= i < a@.len() && i % 2 == 1 ==> #[trigger] sorted@[i] == #[trigger] a@[i],
        a@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fix type mismatches and multiset operations */
{
    let mut result = vec![0i8; a.len()];
    
    // Copy odd-indexed elements unchanged
    for i in 0..a.len()
        invariant
            forall|k: int| 0 <= k < i && k % 2 == 1 ==> result@[k] == a@[k],
            forall|k: int| 0 <= k < i && k % 2 == 0 ==> result@[k] == 0,
    {
        if i % 2 == 1 {
            result.set(i, a[i]);
        }
    }
    
    // Extract even-indexed elements
    let mut evens = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant 
            i % 2 == 0,
            evens@.len() == i / 2,
            forall|j: int| 0 <= j < evens@.len() ==> evens@[j] == a@[2*j],
    {
        evens.push(a[i]);
        i = i + 2;
    }
    
    // Sort the even-indexed elements
    evens.sort();
    
    // Place sorted even-indexed elements back
    let mut i = 0;
    while i < a.len()
        invariant 
            i % 2 == 0,
            forall|k: int| 0 <= k < i && k % 2 == 0 ==> result@[k] == evens@[k/2],
            forall|k: int| 0 <= k < result@.len() && k % 2 == 1 ==> result@[k] == a@[k],
    {
        result.set(i, evens[i/2]);
        i = i + 2;
    }
    
    // Prove multiset preservation
    proof {
        let evens_input = a@.filter(|x: i8| true);
        let odds_input = a@.filter(|x: i8| true);
        let evens_result = result@.filter(|x: i8| true);
        let odds_result = result@.filter(|x: i8| true);
        
        assert(evens_input.to_multiset() == evens@.to_multiset());
        assert(odds_result == odds_input);
        assert(evens_result == evens@);
        assert(a@.to_multiset() == evens_input.to_multiset() + odds_input.to_multiset());
        assert(result@.to_multiset() == evens_result.to_multiset() + odds_result.to_multiset());
        assert(result@.to_multiset() == evens@.to_multiset() + odds_input.to_multiset());
        assert(result@.to_multiset() == evens_input.to_multiset() + odds_input.to_multiset());
        assert(result@.to_multiset() == a@.to_multiset());
    }
    
    result
}
// </vc-code>


}

fn main() {}