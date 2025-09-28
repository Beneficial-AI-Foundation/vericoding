// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Ghost function to compute spec using native i8 operations */
#[verifier::spec]
fn square_spec(x: i8) -> int
    ensures
        square_spec(x) == (#[verifier::spec] x as int) * (#[verifier::spec] x as int),
{
    (#[verifier::spec] x as int) * (#[verifier::spec] x as int)
}
// </vc-helpers>

// <vc-spec>
fn square(arr: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> result[i] as int == arr[i] as int * arr[i] as int,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed spec type annotations and verification */
{
    let mut result = Vec::new();
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            result.len() == index,
            forall|i: int| 0 <= i < index ==> result[i] as int == (#[verifier::spec] arr[i] as int) * (#[verifier::spec] arr[i] as int),
    {
        let elem = arr[index];
        let squared = (elem as i32 * elem as i32) as i8;
        result.push(squared);
        index += 1;
    }
    result
}
// </vc-code>


}
fn main() {}