// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn mod_func(a: Vec<String>, values: Vec<String>) -> (result: Vec<String>)
    requires a.len() == values.len(),
    ensures 
        result.len() == a.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed `as int` casting issue for indexing */
    let mut result = Vec::<String>::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i,
            i <= a.len(),
            result.len() == i,
            a.len() == values.len(),
        decreases a.len() - i
    {
        // Access String elements directly using `[]`, which returns `&String`.
        // Comparison of `&String` works directly.
        if a[i] == values[i] {
            result.push(a[i].clone());
        } else {
            result.push(values[i].clone());
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}