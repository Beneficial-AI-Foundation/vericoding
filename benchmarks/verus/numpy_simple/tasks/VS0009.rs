// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn center(input: Vec<String>, width: usize) -> (result: Vec<String>)
    requires 
        input.len() > 0,
        forall|i: int| 0 <= i < input.len() ==> input[i]@.len() >= 1,
    ensures
        result.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> 
            if input[i]@.len() > width {
                result[i]@.len() == input[i]@.len()
            } else {
                result[i]@.len() == width
            },
        forall|i: int| 0 <= i < input.len() ==> 
            if input[i]@.len() < width {
                let start_pos = (width - input[i]@.len() + 1) / 2;
                result[i]@.skip(start_pos as int).take(input[i]@.len() as int) == input[i]@
            } else {
                true
            }
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}