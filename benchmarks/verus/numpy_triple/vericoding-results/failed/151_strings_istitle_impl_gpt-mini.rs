// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_titlecased(s: Seq<char>) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): is_upper classification */
spec fn is_upper(c: char) -> bool { c >= 'A' && c <= 'Z' }
/* helper modified by LLM (iteration 5): is_lower classification */
spec fn is_lower(c: char) -> bool { c >= 'a' && c <= 'z' }
/* helper modified by LLM (iteration 5): is_alpha classification */
spec fn is_alpha(c: char) -> bool { is_upper(c) || is_lower(c) }
/* helper modified by LLM (iteration 5): titlecase predicate */
spec fn is_titlecased(s: Seq<char>) -> bool { if s.len() == 0 { false } else { is_upper(s@[0]) && (forall|i: int| 1 <= i && i < s.len() ==> (!is_alpha(s@[i]) || is_lower(s@[i]))) } }
// </vc-helpers>

// <vc-spec>
fn istitle(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == is_titlecased(a[i]@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate using int indices and compute is_titlecased for each string */
    let mut result = Vec::<bool>::new();
    let mut i: int = 0;
    while i < a.len()
        invariant 0 <= i && i <= a.len()
        invariant result.len() == i
        invariant forall|j: int| 0 <= j && j < i ==> result[j] == is_titlecased(a[j]@)
        decreases a.len() - i
    {
        let b = is_titlecased(a[i]@);
        result.push(b);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}