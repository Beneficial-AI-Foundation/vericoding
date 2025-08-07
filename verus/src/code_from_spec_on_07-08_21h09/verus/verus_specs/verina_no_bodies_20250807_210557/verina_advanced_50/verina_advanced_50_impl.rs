use vstd::prelude::*;

verus! {

// Helper function to check if a sequence is sorted (pairwise comparison)
spec fn is_sorted(s: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

// Precondition definition - equivalent to List.Pairwise (· ≤ ·) from Lean
spec fn merge_sorted_precond(a1: &Vec<nat>, a2: &Vec<nat>) -> bool {
    is_sorted(a1@) && is_sorted(a2@)
}

// Postcondition definition - sorted result that's a permutation of input concatenation
spec fn merge_sorted_postcond(a1: &Vec<nat>, a2: &Vec<nat>, result: &Vec<nat>) -> bool {
    is_sorted(result@) && 
    result@.to_multiset() == (a1@ + a2@).to_multiset()
}

// The merge function 
fn merge_sorted(a1: &Vec<nat>, a2: &Vec<nat>) -> (result: Vec<nat>)
    requires 
        merge_sorted_precond(a1, a2)
    ensures 
        merge_sorted_postcond(a1, a2, &result)
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove termination */
    while i < a1.len() || j < a2.len()
        invariant
            i <= a1.len(),
            j <= a2.len(),
            is_sorted(result@),
            result@.to_multiset() == (a1@.subrange(0, i as int) + a2@.subrange(0, j as int)).to_multiset(),
            forall|k: int| 0 <= k < result@.len() ==> (
                (i < a1.len() ==> result@[k] <= a1@[i as int]) &&
                (j < a2.len() ==> result@[k] <= a2@[j as int])
            )
        decreases (a1.len() - i) + (a2.len() - j)
    {
        if i >= a1.len() {
            result.push(a2[j]);
            j += 1;
        } else if j >= a2.len() {
            result.push(a1[i]);
            i += 1;
        } else if a1[i] <= a2[j] {
            result.push(a1[i]);
            i += 1;
        } else {
            result.push(a2[j]);
            j += 1;
        }
    }
    
    result
}

// This represents the theorem from Lean - note that in Lean it was left as 'sorry'
// In Verus, the function contract itself serves as the specification
// The theorem is implicitly verified when the function verifies successfully

fn main() {}

} // verus!