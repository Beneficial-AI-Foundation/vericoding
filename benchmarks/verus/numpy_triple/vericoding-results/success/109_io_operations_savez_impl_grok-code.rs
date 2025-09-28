// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn savez(file: String, arr1: Vec<f32>, arr2: Vec<f32>, allow_pickle: bool) -> (result: ())
    requires 
        true,
    ensures 
        result == (),
        exists|recoverable_arr1: Vec<f32>| #[trigger] recoverable_arr1.len() == arr1.len() &&
            forall|i: int| 0 <= i < arr1.len() ==> recoverable_arr1[i] == arr1[i],
        exists|recoverable_arr2: Vec<f32>| #[trigger] recoverable_arr2.len() == arr2.len() &&
            forall|i: int| 0 <= i < arr2.len() ==> recoverable_arr2[i] == arr2[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): provided witnesses for recoverable arrays by using the input arrays, removing verification bypasses */
    proof {
        assert (exists|recoverable_arr1: Vec<f32>| #[trigger] recoverable_arr1.len() == arr1.len() &&
            forall|i: int| 0 <= i < arr1.len() ==> recoverable_arr1@[i] == arr1@[i])
        by {
            let rec = arr1;
            assert(rec.len() == arr1.len());
            assert(forall|i: int| 0 <= i < arr1.len() ==> rec@[i] == arr1@[i]);
        }
        assert (exists|recoverable_arr2: Vec<f32>| #[trigger] recoverable_arr2.len() == arr2.len() &&
            forall|i: int| 0 <= i < arr2.len() ==> recoverable_arr2@[i] == arr2@[i])
        by {
            let rec = arr2;
            assert(rec.len() == arr2.len());
            assert(forall|i: int| 0 <= i < arr2.len() ==> rec@[i] == arr2@[i]);
        }
    }
}
// </vc-code>

}
fn main() {}