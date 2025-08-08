use vstd::prelude::*;

verus! {

fn copy(arr: &[i32]) -> (ret: Vec<i32>)
    ensures
        ret.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> ret[i] == arr[i],
{
    let mut ret = Vec::with_capacity(arr.len());
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            ret.len() == i,
            forall|j: int| 0 <= j < i ==> ret[j] == arr[j],
        decreases arr.len() - i,
    {
        ret.push(arr[i]);
        i = i + 1;
    }
    
    ret
}

}