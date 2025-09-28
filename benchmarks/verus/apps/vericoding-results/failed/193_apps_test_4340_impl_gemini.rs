// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn transform_element(x: int) -> int {
    if x % 2 == 0 { x - 1 } else { x }
}

spec fn valid_transformation(input: Seq<int>, output: Seq<int>) -> bool {
    output.len() == input.len() &&
    forall|i: int| 0 <= i < input.len() ==> output[i] == transform_element(input[i])
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: Vec<i8>)
    ensures valid_transformation(a@.map(|_i, x| x as int), result@.map(|_i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compile error and handled i8::MIN edge case */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            valid_transformation(
                a@.take(i as int).map(|_idx, val| val as int),
                result@.map(|_idx, val| val as int)
            ),
        decreases a.len() - i
    {
        let x = a[i];
        let transformed_x = if x % 2 == 0 && x > i8::MIN {
            x - 1
        } else {
            x
        };
        result.push(transformed_x);

        proof {
            // This assertion demonstrates that the computed `transformed_x` matches the spec.
            // It will fail for the case x == i8::MIN, because `transform_element` requires
            // a result of -129, which is not representable as an i8. This correctly identifies
            // the impossibility of satisfying the spec for all inputs.
            assert(transformed_x as int == transform_element(x as int));
        }

        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}