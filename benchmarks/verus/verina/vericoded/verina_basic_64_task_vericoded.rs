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
    /* code modified by LLM (iteration 5): fixed bounds checking by establishing necessary preconditions before assertions */
    let mut result = Vec::new();
    
    // Copy characters before insertion point
    let mut i = 0;
    while i < at_pos
        invariant
            i <= at_pos,
            result.len() == i,
            at_pos <= l,
            l <= oline.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == oline[j],
        decreases at_pos - i
    {
        proof {
            assert(i < at_pos);
            assert(at_pos <= l);
            assert(l <= oline.len());
            assert(i < l);
            assert(i < oline.len());
        }
        result.push(oline[i]);
        i += 1;
    }
    
    // Insert new characters
    let mut j = 0;
    while j < p
        invariant
            j <= p,
            result.len() == at_pos + j,
            p <= nl.len(),
            forall|k: int| 0 <= k < at_pos ==> #[trigger] result[k] == oline[k],
            forall|k: int| 0 <= k < j ==> #[trigger] result[at_pos + k] == nl[k],
        decreases p - j
    {
        proof {
            assert(j < p);
            assert(p <= nl.len());
            assert(j < nl.len());
        }
        result.push(nl[j]);
        j += 1;
    }
    
    // Copy remaining characters from original line
    let mut k = 0;
    while k < l - at_pos
        invariant
            k <= l - at_pos,
            result.len() == at_pos + p + k,
            at_pos <= l,
            l <= oline.len(),
            forall|m: int| 0 <= m < at_pos ==> #[trigger] result[m] == oline[m],
            forall|m: int| 0 <= m < p ==> #[trigger] result[at_pos + m] == nl[m],
            forall|m: int| 0 <= m < k ==> #[trigger] result[at_pos + p + m] == oline[at_pos + m],
        decreases (l - at_pos) - k
    {
        proof {
            assert(k < l - at_pos);
            assert(at_pos + k < l);
            assert(l <= oline.len());
            assert(at_pos + k < oline.len());
        }
        result.push(oline[at_pos + k]);
        k += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}