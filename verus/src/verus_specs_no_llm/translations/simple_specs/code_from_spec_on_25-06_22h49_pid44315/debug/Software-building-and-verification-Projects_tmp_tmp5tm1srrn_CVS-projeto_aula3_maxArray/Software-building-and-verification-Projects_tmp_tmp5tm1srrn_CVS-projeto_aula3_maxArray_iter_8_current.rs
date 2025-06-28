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
            // Prove that the new max satisfies the invariant
            assert(arr.spec_index(idx as int) == max);
            assert(exists|x: int| 0 <= x < (idx + 1) as int && arr.spec_index(x) == max) by {
                assert(0 <= idx as int < (idx + 1) as int && arr.spec_index(idx as int) == max);
            }
        } else {
            // Prove that the existing witness still works
            assert(exists|x: int| 0 <= x < (idx + 1) as int && arr.spec_index(x) == max) by {
                let old_witness = choose|x: int| 0 <= x < idx as int && arr.spec_index(x) == max;
                assert(0 <= old_witness < (idx + 1) as int && arr.spec_index(old_witness) == max);
            }
        }
        idx += 1;
    }
    
    max
}

}