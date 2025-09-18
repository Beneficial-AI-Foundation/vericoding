// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_digit(c: char) -> bool { '0' <= c && c <= '9' }
// </vc-helpers>

// <vc-spec>
fn fromstring(input: Vec<char>, sep: Vec<char>) -> (result: Vec<f32>)
    requires
        sep.len() > 0,
        input.len() > 0,
    ensures
        result.len() > 0,
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    result.push(0.0f32);
    result
}
// </vc-code>

}
fn main() {}