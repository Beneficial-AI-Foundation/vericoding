use vstd::prelude::*;

verus! {

fn extract(condition: Vec<bool>, arr: Vec<i32>) -> (result: Vec<i32>)
    requires condition.len() == arr.len(),
    ensures

        forall|k: int| 0 <= k < result.len() ==> 
            exists|i: int| 0 <= i < condition.len() && condition[i] && result[k] == arr[i],

        forall|k1: int, k2: int| 0 <= k1 < k2 < result.len() ==>
            exists|i1: int, i2: int| 
                0 <= i1 < i2 < condition.len() && 
                condition[i1] && condition[i2] &&
                result[k1] == arr[i1] && result[k2] == arr[i2],

        forall|i: int| 0 <= i < condition.len() && condition[i] ==>
            exists|k: int| 0 <= k < result.len() && result[k] == arr[i]
{
    assume(false);
    unreached()
}

}
fn main() {}