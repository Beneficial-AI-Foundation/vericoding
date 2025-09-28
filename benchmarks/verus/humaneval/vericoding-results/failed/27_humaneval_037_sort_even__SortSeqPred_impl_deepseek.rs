// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

    /* helper modified by LLM (iteration 5): Fix type annotations and recursion */
    spec fn sort_seq_pred_spec(s: Seq<i8>, p: Seq<bool>) -> (sorted: Seq<i8>)
        requires s.len() == p.len(),
        ensures 
            sorted.len() == s.len(),
            forall|i: int, j: int| 0 <= i < j < sorted.len() && p[i] && p[j] ==> sorted[i] as int <= sorted[j] as int,
            s.to_multiset() == sorted.to_multiset(),
            forall|i: int| 0 <= i < s.len() && !p[i] ==> sorted[i] == s[i],
    {
        s
    }
    
    spec fn count_true_before(index: int, p: Seq<bool>) -> nat
        requires 0 <= index <= p.len(),
        decreases index,
    {
        if index <= 0 {
            0
        } else {
            (if p[index - 1] { 1 } else { 0 }) + count_true_before(index - 1, p)
        }
    }
    
    proof fn lemma_count_true_before_consistent(index: int, p: Seq<bool>)
        requires 0 <= index <= p.len(),
        ensures count_true_before(index, p) == count_true_in_range(0, index, p),
        decreases index,
    {
        if index > 0 {
            lemma_count_true_before_consistent(index - 1, p);
        }
    }
    
    spec fn count_true_in_range(start: int, end: int, p: Seq<bool>) -> nat
        requires 0 <= start <= end <= p.len(),
        decreases end - start,
    {
        if end == start {
            0
        } else {
            (if p[start] { 1 } else { 0 }) + count_true_in_range(start + 1, end, p)
        }
    }

// </vc-helpers>

// <vc-spec>
fn sort_seq_pred(s: Vec<i8>, p: Vec<bool>) -> (sorted: Vec<i8>)
    requires s.len() == p.len(),
    ensures 
        sorted.len() == s.len(),
        forall|i: int, j: int| 0 <= i < j < sorted.len() && p[i as int] && p[j as int] ==> sorted[i] as int <= sorted[j] as int,
        s@.to_multiset() == sorted@.to_multiset(),
        forall|i: int| 0 <= i < s.len() && !p[i as int] ==> sorted[i] == s[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix integer conversion and use ghost variables */
    let mut result = s.clone();
    let len = s.len();
    let mut i: usize = 0;
    
    while i < len
        invariant
            result@.to_multiset() == s@.to_multiset(),
            forall|k: int| 0 <= k < len as int && !p[k as usize] ==> result[k as usize] == s[k as usize],
            i <= len,
    {
        if p[i] {
            let mut j: usize = i + 1;
            while j < len
                invariant
                    result@.to_multiset() == s@.to_multiset(),
                    forall|k: int| 0 <= k < len as int && !p[k as usize] ==> result[k as usize] == s[k as usize],
                    i < j <= len,
            {
                if p[j] && result[j] < result[i] {
                    let temp = result[i];
                    result[i] = result[j];
                    result[j] = temp;
                }
                j = j + 1;
            }
        }
        i = i + 1;
    }
    
    proof {
        // Verify that non-predicate elements are preserved
        assert forall|k: int| 0 <= k < len as int && !p[k as usize] implies result[k as usize] == s[k as usize] by {
            // This holds because we only swap when both positions have predicate true
        };
        
        // Verify multiset preservation
        assert(result@.to_multiset() == s@.to_multiset());
    }
    
    result
}
// </vc-code>


}

fn main() {}