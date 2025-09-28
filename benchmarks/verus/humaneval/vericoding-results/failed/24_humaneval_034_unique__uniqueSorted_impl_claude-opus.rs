// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn distinct(s: Seq<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}

/* helper modified by LLM (iteration 5): kept distinct predicate */
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
    /* code modified by LLM (iteration 5): added trigger annotation to fix quantifier */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    
    if s.len() == 0 {
        return result;
    }
    
    result.push(s[0]);
    i = 1;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result@.len() >= 1,
            distinct(result@),
            forall|k: int, l: int| 0 <= k < l < result@.len() ==> result@[k] < result@[l],
            forall|x: i8| result@.contains(x) ==> s@.contains(x),
            forall|x: i8| s@.subrange(0, i as int).contains(x) ==> result@.contains(x),
            result@[result@.len() - 1] == s@[i - 1],
            forall|j: int| i <= j < s@.len() ==> #[trigger] s@[j] >= s@[i - 1],
        decreases s.len() - i
    {
        if s[i] != result[result.len() - 1] {
            result.push(s[i]);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}