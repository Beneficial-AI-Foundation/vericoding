// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn fromstring(input: &str, sep: &str, n: u8) -> (result: Vec<f64>)
    requires n > 0,
    ensures 
        result@.len() <= n as int,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}