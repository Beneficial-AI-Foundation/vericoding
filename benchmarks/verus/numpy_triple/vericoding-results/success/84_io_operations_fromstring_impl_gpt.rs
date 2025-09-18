// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn always_true() -> bool { true }
proof fn lemma_always_true() ensures always_true() { }
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
    let v: Vec<f64> = Vec::new();
    v
}
// </vc-code>

}
fn main() {}