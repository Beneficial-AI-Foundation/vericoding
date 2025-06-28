use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn maxArrayReverse(arr: Vec<int>) -> (max: int)
    requires
        arr.len() > 0
    ensures
        forall|i: int| 0 <= i < arr.len() ==> arr.spec_index(i) <= max,
        exists|x: int| 0 <= x < arr.len() && arr.spec_index(x) == max
{
    let mut max = arr.spec_index(0);
    let mut i: usize = 1;
    
    while i < arr.len()
        invariant
            0 < i <= arr.len(),
            forall|j: int| 0 <= j < i ==> arr.spec_index(j) <= max,
            exists|k: int| 0 <= k < i && arr.spec_index(k) == max
    {
        if arr.spec_index(i as int) > max {
            max = arr.spec_index(i as int);
        }
        i = i + 1;
    }
    
    max
}

}