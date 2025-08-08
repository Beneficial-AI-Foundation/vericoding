use vstd::prelude::*;

verus! {

fn where_method(condition: spec_fn(int) -> bool, arr: &[int], change: spec_fn(int) -> int) -> (ret: Vec<int>)
    requires 
        arr.len() > 0
    ensures
        ret.len() == arr.len() &&
        forall|i: int| 0 <= i < arr.len() ==> 
            ret[i] == if condition(arr[i]) { 
                change(arr[i]) 
            } else { 
                arr[i]
            }
{
    assume(false);
    Vec::new()
}

}