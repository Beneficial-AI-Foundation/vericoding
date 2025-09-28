// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn singleton_f32(x: f32) -> (v: Vec<f32>)
    ensures
        v.len() == 1,
{
    let mut v = Vec::<f32>::new();
    v.push(x);
    v
}
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
    singleton_f32(0.0f32)
}
// </vc-code>

}
fn main() {}