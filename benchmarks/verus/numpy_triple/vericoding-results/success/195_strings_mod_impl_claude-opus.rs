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
    /* code modified by LLM (iteration 3): added decreases clause to fix loop verification */
    let mut result: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            a.len() == values.len(),
        decreases a.len() - i,
    {
        let new_str = if a[i] == values[i] {
            "".to_string()
        } else {
            a[i].clone()
        };
        result.push(new_str);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}