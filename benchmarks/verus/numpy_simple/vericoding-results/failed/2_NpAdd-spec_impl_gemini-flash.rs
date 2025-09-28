// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): none needed */
// </vc-helpers>

// <vc-spec>
fn add(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == a[i] as int + b[i] as int
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Add missing `pop_element` after push to ensure postconditions are met */
{
    let mut result_vec: Vec<i8> = Vec::new();
    let mut i = 0;

    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result_vec.len() == i,
            // The elements of result_vec up to i-1 are correctly computed
            forall|j: int| 0 <= j < i ==> result_vec[j] as int == a[j] as int + b[j] as int
        decreases a.len() - i
    {
        // Verus needs to be convinced that a[i] + b[i] does not overflow/underflow i8
        // The ensures clause uses `as int` conversion, so we apply that here for safety
        // The sum needs to fit into i8
        proof {
            let sum_as_int = (a[i] as int) + (b[i] as int);
            // Assert that the sum fits within the bounds of i8.
            // If not, this assertion will fail, indicating a need for a different type or error handling.
            assert(sum_as_int >= i8::MIN as int && sum_as_int <= i8::MAX as int);
        }

        let val_to_push = ((a[i] as int) + (b[i] as int)) as i8;
        result_vec.push(val_to_push);
        proof { 
            result_vec.pop_element();
        }
        
        i = i + 1;
    }

    proof {
        assert(result_vec.len() == a.len());
        // The forall guarantee comes from the loop invariant.
    }

    result_vec
}
// </vc-code>


}
fn main() {}