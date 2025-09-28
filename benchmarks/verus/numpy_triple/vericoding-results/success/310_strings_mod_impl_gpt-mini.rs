// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): clone a String by reference */
fn clone_string(s: &String) -> String {
    s.clone()
}
// </vc-helpers>

// <vc-spec>
fn mod_func(a: Vec<String>, values: Vec<String>) -> (result: Vec<String>)
    requires a.len() == values.len(),
    ensures 
        result.len() == a.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): iterate indices with invariant linking lengths */
    let mut result: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.len() == i,
            i <= a.len(),
            a.len() == values.len(),
        decreases a.len() - i
    {
        result.push(clone_string(&values[i]));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}