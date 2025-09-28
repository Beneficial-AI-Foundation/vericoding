// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mod_func(a: Vec<String>, values: Vec<String>) -> (result: Vec<String>)
    requires a.len() == values.len(),
    ensures 
        result.len() == a.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut result: Vec<String> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
        decreases a.len() - i
    {
        result.push(a[i].clone());
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}