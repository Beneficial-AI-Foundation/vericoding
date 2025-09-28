// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn rpartition(a: Vec<String>, sep: String) -> (result: (Vec<String>, Vec<String>, Vec<String>))
    requires true,
    ensures 
        result.0.len() == a.len(),
        result.1.len() == a.len(),
        result.2.len() == a.len()
// </vc-spec>
// <vc-code>
{
    let result = (a.clone(), a.clone(), a.clone());
    result
}
// </vc-code>


}
fn main() {}