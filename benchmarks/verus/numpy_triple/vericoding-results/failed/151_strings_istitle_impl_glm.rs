// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_titlecased(s: Seq<char>) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed char method calls by removing vstd:: prefix */
fn is_titlecased_exec(s: &str) -> (b: bool)
    ensures b == is_titlecased(s@)
{
    let chars = s.chars();
    let mut iter = chars.into_iter();
    match iter.next() {
        None => true,
        Some(first) => {
            if !char::is_uppercase(first) {
                false
            } else {
                for c in iter {
                    if !char::is_lowercase(c) {
                        return false;
                    }
                }
                true
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn istitle(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == is_titlecased(a[i]@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Using fixed helper function with correct char methods */
{
    let mut result = Vec::with_capacity(a.len());
    for i in 0..a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == is_titlecased(a[j]@)
    {
        let s = &a[i];
        let b = is_titlecased_exec(s);
        result.push(b);
    }
    result
}
// </vc-code>

}
fn main() {}