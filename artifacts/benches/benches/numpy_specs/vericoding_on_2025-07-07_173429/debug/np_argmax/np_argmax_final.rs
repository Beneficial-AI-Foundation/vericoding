use vstd::prelude::*;

verus! {

fn argmax(arr: &Vec<i32>) -> (ret: usize)
    requires
        arr.len() > 0,
    ensures
        ret < arr.len(),
        forall|i: int| 0 <= i < ret ==> arr[ret as int] > arr[i],
        forall|i: int| ret < i < arr.len() ==> arr[ret as int] >= arr[i],
{
    let mut ret: usize = 0;
    let mut j: usize = 1;
    
    while j < arr.len()
        invariant
            0 <= ret < arr.len(),
            1 <= j <= arr.len(),
            forall|i: int| 0 <= i < ret ==> arr[ret as int] > arr[i],
            forall|i: int| ret < i < j ==> arr[ret as int] >= arr[i],
        decreases arr.len() - j,
    {
        if arr[j] > arr[ret] {
            ret = j;
        }
        j = j + 1;
    }
    
    ret
}

fn main() {
}

}