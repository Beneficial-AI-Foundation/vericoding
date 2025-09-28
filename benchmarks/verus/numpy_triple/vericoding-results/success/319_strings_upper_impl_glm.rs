// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn string_to_upper(s: Seq<char>) -> Seq<char> {
    s
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): replaced String::len with view len */
fn exec_string_to_upper(s: String) -> (result: String)
    ensures
        result@ == string_to_upper(s@),
        result@.len() == s@.len()
{
    s
}
// </vc-helpers>

// <vc-spec>
fn upper(a: Vec<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() as int ==>
            result@[i]@ == string_to_upper(a@[i]@) &&
            result@[i]@.len() == a@[i]@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added bound on i in loop invariant */
    let mut result: Vec<String> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result@[j]@ == string_to_upper(a@[j]@) && 
                result@[j]@.len() == a@[j]@.len(),
        decreases (a.len() - i) as nat
    {
        let s = a[i].clone();
        let t = exec_string_to_upper(s);
        result.push(t);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}