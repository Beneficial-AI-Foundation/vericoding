// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn genfromtxt(input: Vec<String>, delimiter: String, fill_value: f32, skip_header: usize) -> (result: Vec<Vec<f32>>)
    requires 
        skip_header < input.len(),
    ensures
        result.len() == input.len() - skip_header,
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] (i + skip_header as int) >= skip_header as int,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}