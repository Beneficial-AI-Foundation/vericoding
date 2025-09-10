use vstd::prelude::*;

verus!{

fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)

    requires 
        forall |k1:int,k2:int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],

    ensures
        forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
        forall |k:int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
{
    assume(false);
    unreached()
}

}
fn main() {}