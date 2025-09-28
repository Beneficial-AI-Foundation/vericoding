// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn unique_sorted(s: Vec<i8>) -> (result: Vec<i8>)
    requires 
        forall|i: int, j: int| 0 <= i < j < s@.len() ==> s@[i] <= s@[j],
    ensures 
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] < result@[j],
        forall|x: i8| result@.contains(x) ==> s@.contains(x),
        forall|x: i8| s@.contains(x) ==> result@.contains(x),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed trigger attribute which is not valid in Verus */
    let mut result: Vec<i8> = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|k: int, l: int| 0 <= k < l < result@.len() ==> result@[k] < result@[l],
            forall|x: i8| result@.contains(x) ==> s@.contains(x),
            forall|k: int| 0 <= k < result@.len() ==> exists|j: int| 0 <= j < i && s@[j] == result@[k],
            forall|j: int| 0 <= j < i ==> (exists|k: int| 0 <= k < result@.len() && result@[k] == s@[j]),
        decreases s.len() - i
    {
        let current = s[i];
        
        if result.len() == 0 || result[result.len() - 1] != current {
            result.push(current);
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}