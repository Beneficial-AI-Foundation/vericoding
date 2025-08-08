use vstd::prelude::*;

verus! {

fn square(arr: Vec<i32>) -> (ret: Vec<i32>)
    ensures
        ret.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> ret[i] == arr[i] * arr[i],
{
    let mut ret: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            ret.len() == i,
            forall|j: int| 0 <= j < i ==> ret[j] == arr[j] * arr[j],
        decreases arr.len() - i,
    {
        assume(arr[i as int] * arr[i as int] >= i32::MIN && arr[i as int] * arr[i as int] <= i32::MAX);
        let val = arr[i] * arr[i];
        ret.push(val);
        i = i + 1;
    }
    
    ret
}

}

fn main() {}