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
proof fn lemma_forall_trigger(input: Seq<int>, output: Seq<int>)
    requires
        output.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> output[i] == transform_element(input[i]),
    ensures
        valid_transformation(input, output),
{
    // trivial
}
/* helper modified by LLM (iteration 5): kept helper function as it correctly proves the transformation validity */
// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: Vec<i8>)
    ensures valid_transformation(a@.map(|_i, x| x as int), result@.map(|_i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed trigger syntax from #![trigger] to #[trigger] */
    let mut result = Vec::with_capacity(a.len());
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                #[trigger result[j]] 
                result[j] as int == transform_element(a[j] as int),
        decreases a.len() - i
    {
        let x = a[i];
        if x % 2 == 0 {
            result.push(x.wrapping_sub(1));
        } else {
            result.push(x);
        }
        assert(result[i] as int == transform_element(a[i] as int));
        i += 1;
    }
    proof {
        lemma_forall_trigger(a@.map(|_i, x| x as int), result@.map(|_i, x| x as int));
    }
    result
}
// </vc-code>


}

fn main() {}