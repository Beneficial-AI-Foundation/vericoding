use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn maxArrayReverse(arr: Vec<int>) -> (max: int)
    requires
        arr.len() > 0
    ensures
        forall i: int :: 0 <= i < arr.len() ==> arr.spec_index(i) <= max,
        exists x::0 <= x < arr.len() && arr.spec_index(x) == max
{
    let mut max = arr[0];
    let mut i = 1;
    
    while i < arr.len()
        invariant
            0 < i <= arr.len(),
            forall j: int :: 0 <= j < i ==> arr.spec_index(j) <= max,
            exists k: int :: 0 <= k < i && arr.spec_index(k) == max
    {
        if arr[i] > max {
            max = arr[i];
        }
        i = i + 1;
    }
    
    max
}

}