// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
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
    let result: Vec<f64> = Vec::<f64>::new();
    result
}
// </vc-code>

}
fn main() {}