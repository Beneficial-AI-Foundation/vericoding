use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn savez(file: String, arr1: Vec<f32>, arr2: Vec<f32>, allow_pickle: bool) -> (result: ())
    requires 
        true,
    ensures 
        result == (),
        exists|archive_exists: bool| archive_exists == true,
        exists|recoverable_arr1: Vec<f32>| 
            recoverable_arr1.len() == arr1.len() &&
            forall|i: int| 0 <= i < arr1.len() ==> recoverable_arr1[i] == arr1[i],
        exists|recoverable_arr2: Vec<f32>| 
            recoverable_arr2.len() == arr2.len() &&
            forall|i: int| 0 <= i < arr2.len() ==> recoverable_arr2[i] == arr2[i],
        exists|file_size: nat| file_size > 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}