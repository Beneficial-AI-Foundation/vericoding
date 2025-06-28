use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn maxArray(arr: Vec<int>) -> (max: int)
    requires
        arr.len() > 0
    ensures
        forall|i: int| 0 <= i < arr.len() ==> arr.spec_index(i) <= max,
        exists|x: int| 0 <= x < arr.len() && arr.spec_index(x) == max
{
    let mut max = arr[0];
    let mut idx: usize = 1;
    
    while idx < arr.len()
        invariant
            1 <= idx <= arr.len(),
            forall|i: int| 0 <= i < idx ==> arr.spec_index(i) <= max,
            exists|x: int| 0 <= x < idx && arr.spec_index(x) == max
    {
        if arr[idx] > max {
            max = arr[idx];
        }
        idx += 1;
    }
    
    // After the loop, we need to establish that the postcondition holds
    // The loop invariant tells us the property holds for indices 0..idx
    // Since idx == arr.len() after the loop, this covers all valid indices
    assert(idx == arr.len());
    assert(forall|i: int| 0 <= i < arr.len() ==> arr.spec_index(i) <= max);
    assert(exists|x: int| 0 <= x < arr.len() && arr.spec_index(x) == max);
    
    max
}

}