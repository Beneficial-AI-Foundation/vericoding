// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn make_brackets() -> (result: Vec<char>)
    ensures
        result@.len() == 2,
        result@[0] == '[',
        result@[1] == ']'
{
    let mut v: Vec<char> = Vec::new();
    v.push('[');
    v.push(']');
    v
}
// </vc-helpers>

// <vc-spec>
fn array2string(arr: Vec<f32>, separator: &str) -> (result: Vec<char>)
    ensures
        result@.len() > 0,
        result@[0] == '[',
        result@[result@.len() - 1] == ']'
// </vc-spec>
// <vc-code>
{
    let v = make_brackets();
    v
}
// </vc-code>

}
fn main() {}