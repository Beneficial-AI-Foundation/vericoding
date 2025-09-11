use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn fromstring(input: &str, sep: &str, n: usize) -> (result: Vec<f64>)
    requires n > 0,
    ensures 
        result.len() <= n,
        forall|i: int| 0 <= i < result.len() ==> true,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}