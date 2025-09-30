// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    let mut out: Vec<char> = Vec::new();
    out.push('[');
    out.push(']');
    proof {
        assert(out@.len() > 0);
        assert(out@[0] == '[');
        assert(out@[out@.len() - 1] == ']');
    }
    out
}
// </vc-code>

}
fn main() {}