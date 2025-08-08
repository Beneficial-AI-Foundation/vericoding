use vstd::prelude::*;

verus! {

// SPEC
fn copy(arr: &Vec<i32>) -> (ret: Vec<i32>)
    ensures
        ret.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> ret[i] == arr[i],
{
    let mut result = Vec::new();
    let mut idx = 0;
    
    while idx < arr.len()
        invariant
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> result[i] == arr[i],
    {
        result.push(arr[idx]);
        idx += 1;
    }
    
    result
}

fn main() {}

}