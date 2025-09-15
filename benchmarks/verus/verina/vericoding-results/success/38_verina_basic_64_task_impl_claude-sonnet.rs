// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn insert(oline: &Vec<char>, l: usize, nl: &Vec<char>, p: usize, at_pos: usize) -> (result: Vec<char>)
    requires
        l <= oline.len(),
        p <= nl.len(),
        at_pos <= l,
    ensures
        result.len() == l + p,
        forall|i: int| 0 <= i < p ==> #[trigger] result[at_pos + i] == nl[i],
        forall|i: int| 0 <= i < at_pos ==> #[trigger] result[i] == oline[i],
        forall|i: int| 0 <= i < (l - at_pos) ==> #[trigger] result[at_pos + p + i] == oline[at_pos + i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added bounds checks to fix indexing precondition failures */
    let mut result = Vec::new();
    
    // Copy characters before insertion point
    for i in 0..at_pos
        invariant
            result.len() == i,
            i <= at_pos,
            at_pos <= l,
            l <= oline.len(),
            forall|j: int| 0 <= j < i ==> result@[j] == oline@[j],
    {
        assert(i < at_pos && at_pos <= l && l <= oline.len());
        assert(i < oline.len());
        result.push(oline[i]);
    }
    
    // Insert new characters
    for i in 0..p
        invariant
            result.len() == at_pos + i,
            i <= p,
            p <= nl.len(),
            forall|j: int| 0 <= j < at_pos ==> result@[j] == oline@[j],
            forall|j: int| 0 <= j < i ==> result@[at_pos + j] == nl@[j],
    {
        assert(i < p && p <= nl.len());
        assert(i < nl.len());
        result.push(nl[i]);
    }
    
    // Copy remaining characters from original line
    for i in at_pos..l
        invariant
            result.len() == p + i,
            i <= l,
            l <= oline.len(),
            forall|j: int| 0 <= j < at_pos ==> result@[j] == oline@[j],
            forall|j: int| 0 <= j < p ==> result@[at_pos + j] == nl@[j],
            forall|j: int| at_pos <= j < i ==> result@[at_pos + p + (j - at_pos)] == oline@[j],
    {
        assert(i < l && l <= oline.len());
        assert(i < oline.len());
        result.push(oline[i]);
    }
    
    proof {
        assert(result.len() == at_pos + p + (l - at_pos));
        assert(result.len() == l + p);
        
        // Prove final postconditions
        assert(forall|j: int| 0 <= j < at_pos ==> result@[j] == oline@[j]);
        assert(forall|j: int| 0 <= j < p ==> result@[at_pos + j] == nl@[j]);
        assert(forall|j: int| at_pos <= j < l ==> result@[at_pos + p + (j - at_pos)] == oline@[j]);
    }
    
    result
}
// </vc-code>

}
fn main() {}