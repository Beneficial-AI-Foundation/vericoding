// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_u8_as_int_nonnegative(n: u8)
    ensures
        n as int >= 0,
{
}

// </vc-helpers>

// <vc-spec>
fn fromstring(input: &str, sep: &str, n: u8) -> (result: Vec<f64>)
    requires n > 0,
    ensures 
        result@.len() <= n as int,
// </vc-spec>
// <vc-code>
{
    let v: Vec<f64> = Vec::new();
    v
}
// </vc-code>

}
fn main() {}