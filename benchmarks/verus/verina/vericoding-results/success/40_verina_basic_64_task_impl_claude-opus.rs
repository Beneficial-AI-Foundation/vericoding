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
    /* code modified by LLM (iteration 2): Added decreases clauses to all loops */
    let mut result = Vec::new();
    
    // Copy elements from oline[0..at_pos]
    let mut i = 0;
    while i < at_pos
        invariant
            i <= at_pos,
            at_pos <= l,
            l <= oline.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == oline[j],
        decreases at_pos - i
    {
        result.push(oline[i]);
        i = i + 1;
    }
    
    // Copy elements from nl[0..p]
    let mut j = 0;
    while j < p
        invariant
            j <= p,
            p <= nl.len(),
            result.len() == at_pos + j,
            forall|k: int| 0 <= k < at_pos ==> #[trigger] result[k] == oline[k],
            forall|k: int| 0 <= k < j ==> #[trigger] result[at_pos + k] == nl[k],
        decreases p - j
    {
        result.push(nl[j]);
        j = j + 1;
    }
    
    // Copy elements from oline[at_pos..l]
    let mut k = at_pos;
    while k < l
        invariant
            at_pos <= k <= l,
            l <= oline.len(),
            result.len() == at_pos + p + (k - at_pos),
            forall|m: int| 0 <= m < at_pos ==> #[trigger] result[m] == oline[m],
            forall|m: int| 0 <= m < p ==> #[trigger] result[at_pos + m] == nl[m],
            forall|m: int| 0 <= m < (k - at_pos) ==> #[trigger] result[at_pos + p + m] == oline[at_pos + m],
        decreases l - k
    {
        result.push(oline[k]);
        k = k + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}