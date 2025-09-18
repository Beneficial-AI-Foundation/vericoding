// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn fromstring(input: &str, sep: &str, n: usize) -> (result: Vec<f64>)
    requires n > 0,
    ensures 
        result.len() <= n,
        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> true,
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    result
}
// </vc-code>

}
fn main() {}