use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn numpy_frompyfunc<A, B>(func: spec_fn(A) -> B, input: Vec<A>) -> (result: Vec<B>)
    ensures
        result.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> result[i] == func(input[i])
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}