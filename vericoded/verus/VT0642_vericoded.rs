// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): create singleton Vec<String> by consuming an existing String to avoid String::new */
fn singleton_vec_from_string(s: String) -> (v: Vec<String>)
    ensures
        v@.len() == 1,
{
    let mut v: Vec<String> = Vec::new();
    v.push(s);
    v
}
// </vc-helpers>

// <vc-spec>
fn splitlines(a: Vec<String>, keepends: bool) -> (result: Vec<Vec<String>>)
    requires a@.len() > 0,
    ensures 
        result@.len() == a@.len(),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i]@.len() >= 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): build each inner vector from strings popped from the input vector to avoid creating new Strings and maintain the required invariants */
    let mut b: Vec<String> = a;
    let mut result: Vec<Vec<String>> = Vec::new();
    while b.len() > 0
        invariant
            result@.len() + b@.len() == a@.len(),
            forall|j: int| 0 <= j < result@.len() ==> #[trigger] result@[j]@.len() >= 1,
        decreases b@.len()
    {
        let opt = b.pop();
        match opt {
            Option::Some(s) => {
                let inner: Vec<String> = singleton_vec_from_string(s);
                result.push(inner);
            }
            Option::None => {
                // unreachable due to loop condition and pop precondition
            }
        }
    }
    result
}
// </vc-code>

}
fn main() {}