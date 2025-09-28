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
/* helper modified by LLM (iteration 5): removed unnecessary cast to i8 */
spec fn transform_element_i8(x: i8) -> i8 {
    if x % 2 == 0 { x - 1 } else { x }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: Vec<i8>)
    ensures valid_transformation(a@.map(|_i, x| x as int), result@.map(|_i, x| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed `push_view()` error by accessing `result@` directly */
{
    let mut result = Vec::new();
    let mut i = 0;

    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == transform_element_i8(a@[j]),
    {
        let val: i8 = a[i];
        let transformed_val: i8 = transform_element_i8(val);
        result.push(transformed_val);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}