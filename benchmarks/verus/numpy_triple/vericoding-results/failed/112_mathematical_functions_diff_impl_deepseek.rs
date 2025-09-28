// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed loop invariant bounds and access patterns */
fn diff_helper(a: &Vec<i8>, result: &mut Vec<i8>) -> (j: usize)
    requires
        old(result)@.len() == 0,
        a@.len() >= 2,
    ensures
        j == a@.len() - 1,
        result@.len() == j,
        forall|k: int| 0 <= k < j ==> result@[k] == a@[k + 1] - a@[k],
    decreases a@.len() - 0,
{
    let mut i: usize = 0;
    let len = a.len();
    
    while i < len - 1
        invariant
            0 <= i <= len - 1,
            result@.len() == i,
            forall|k: int| 0 <= k < i ==> k + 1 < len && result@[k] == a@[k + 1] - a@[k],
        decreases (len - 1) - i,
    {
        assert(0 <= i < len - 1);
        assert(i + 1 < len);
        let diff = a[i + 1] - a[i];
        result.push(diff);
        i = i + 1;
    }
    
    i
}
// </vc-helpers>

// <vc-spec>
fn numpy_diff(a: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() >= 2,
    ensures 
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == a[i + 1] as int - a[i] as int,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No functional changes, maintaining consistency */
{
    let mut result: Vec<i8> = Vec::new();
    let j = diff_helper(&a, &mut result);
    proof {
        assert(result@.len() == j);
        assert(j == a@.len() - 1);
    }
    result
}
// </vc-code>


}
fn main() {}