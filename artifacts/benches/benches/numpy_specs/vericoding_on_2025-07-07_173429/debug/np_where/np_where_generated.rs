use vstd::prelude::*;

verus! {

fn where_array(
    arr: &Vec<i32>,
) -> (ret: Vec<i32>)
    requires 
        arr.len() > 0,
    ensures
        ret.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> 
            if arr[i] > 10 {
                ret[i] == arr[i] - 1
            } else {
                ret[i] == arr[i]
            },
{
    let mut ret = Vec::with_capacity(arr.len());
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant 
            0 <= i <= arr.len(),
            ret.len() == i,
            forall|j: int| 0 <= j < i ==> 
                if arr[j] > 10 {
                    ret[j] == arr[j] - 1
                } else {
                    ret[j] == arr[j]
                },
        decreases arr.len() - i,
    {
        if arr[i] > 10 {
            ret.push(arr[i] - 1);
        } else {
            ret.push(arr[i]);
        }
        i = i + 1;
    }
    
    ret
}

fn main() {}

}