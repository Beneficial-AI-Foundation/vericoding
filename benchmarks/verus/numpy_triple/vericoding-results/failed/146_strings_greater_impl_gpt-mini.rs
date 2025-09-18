// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added no-op uninterpreted helper */
uninterp spec fn helper_uninterp() -> bool;
// </vc-helpers>

// <vc-spec>
spec fn string_compare_gt(s1: Seq<char>, s2: Seq<char>) -> bool;

fn greater(x1: &Vec<String>, x2: &Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),

        forall|i: int| 0 <= i < result.len() ==> 
            result[i] == string_compare_gt(x1[i]@, x2[i]@),

        forall|i: int| 0 <= i < result.len() ==> 
            result[i] ==> !string_compare_gt(x2[i]@, x1[i]@),

        forall|i: int| 0 <= i < result.len() ==> 
            (x1[i]@ == x2[i]@) ==> (result[i] == false),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterative construction with loop invariant to establish relation to spec */
    let mut result: Vec<bool> = Vec::new();
    let n: int = x1.len();
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n;
        invariant result.len() == i;
        invariant forall|j: int| 0 <= j && j < i ==> result[j] == string_compare_gt(x1[j]@, x2[j]@);
        decreases n - i
    {
        let b: bool = string_compare_gt(x1[i]@, x2[i]@);
        result.push(b);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}