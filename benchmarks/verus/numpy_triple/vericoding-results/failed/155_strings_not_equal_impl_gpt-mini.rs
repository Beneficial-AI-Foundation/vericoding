// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple string inequality helper */
fn neq(a: String, b: String) -> bool { a != b }
// </vc-helpers>

// <vc-spec>
fn not_equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] != x2[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build boolean vector of string inequalities with correct invariants */
    let mut res: Vec<bool> = Vec::new();
    let mut i: nat = 0;
    while i < x1.len()
        invariant i <= x1.len();
        invariant res.len() == i;
        invariant forall |j: nat| j < i ==> res[j] == (x1[j] != x2[j]);
    {
        let b: bool = x1[i] != x2[i];
        res.push(b);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}