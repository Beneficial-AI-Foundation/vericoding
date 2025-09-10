use vstd::prelude::*;

verus! {

fn intersect1d(ar1: Vec<i32>, ar2: Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int| 0 <= i < result.len() ==> 
            (exists|j: int| 0 <= j < ar1.len() && result[i] == ar1[j]) &&
            (exists|l: int| 0 <= l < ar2.len() && result[i] == ar2[l]),

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],

        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && i != j ==> result[i] != result[j],

        forall|val: i32| 
            (exists|i: int| 0 <= i < ar1.len() && ar1[i] == val) && 
            (exists|j: int| 0 <= j < ar2.len() && ar2[j] == val) ==>
            (exists|l: int| 0 <= l < result.len() && result[l] == val)
{
    assume(false);
    unreached();
}

}
fn main() {}