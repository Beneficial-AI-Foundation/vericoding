// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_titlecased(s: Seq<char>) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert Rust String to Seq<char> for spec functions */
spec fn string_seq(s: String) -> Seq<char> {
    s@
}
// </vc-helpers>

// <vc-spec>
fn istitle(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == is_titlecased(a[i]@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate over vector and use spec-level indexing in invariants */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i as int ==> result@[k] == is_titlecased(a@[k]@),
        decreases a.len() - i
    {
        let b = is_titlecased(string_seq(a[i].clone()));
        result.push(b);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}