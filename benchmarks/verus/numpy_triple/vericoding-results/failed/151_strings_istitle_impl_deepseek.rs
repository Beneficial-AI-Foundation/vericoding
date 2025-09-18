// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_titlecased(s: Seq<char>) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Keep only one uninterp spec fn and remove helper functions */
#[verifier(uninterp)]
spec fn is_titlecased(s: Seq<char>) -> bool;
// </vc-helpers>

// <vc-spec>
fn istitle(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == is_titlecased(a[i]@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Direct verification with uninterp spec */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == is_titlecased(a[j]@)
    {
        let s = &a[i];
        result.push(is_titlecased(s@));
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}