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
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            i == result.len(),
            a.len() == values.len(),
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