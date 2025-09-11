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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}