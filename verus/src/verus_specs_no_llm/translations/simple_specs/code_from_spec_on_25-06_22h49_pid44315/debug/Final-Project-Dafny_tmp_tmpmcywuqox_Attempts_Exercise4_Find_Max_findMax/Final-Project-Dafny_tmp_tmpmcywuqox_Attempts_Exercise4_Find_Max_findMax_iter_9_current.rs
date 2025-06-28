use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn findMax(a: Vec<int>) -> (pos: int, maxVal: int)
    requires
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) >= 0
    ensures
        forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) <= maxVal,
        exists|i: int| 0 <= i < a.len() && a.spec_index(i) == maxVal,
        0 <= pos < a.len(),
        a.spec_index(pos) == maxVal
{
    let mut maxPos: usize = 0;
    let mut maxValue: int = a[0];
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            0 <= maxPos < a.len(),
            maxValue == a.spec_index(maxPos as int),
            forall|j: int| 0 <= j < i ==> a.spec_index(j) <= maxValue,
            exists|j: int| 0 <= j < i && a.spec_index(j) == maxValue,
            1 <= i <= a.len(),
            maxValue >= 0
    {
        if a[i] > maxValue {
            maxPos = i;
            maxValue = a[i];
        }
        i = i + 1;
    }
    
    // Proof assertions to help verify postconditions
    assert(maxValue == a.spec_index(maxPos as int));
    assert(0 <= maxPos < a.len());
    assert(exists|j: int| 0 <= j < a.len() && a.spec_index(j) == maxValue);
    
    // Prove that maxValue is indeed the maximum
    assert(forall|j: int| 0 <= j < a.len() ==> a.spec_index(j) <= maxValue) by {
        assert(forall|j: int| 0 <= j < i ==> a.spec_index(j) <= maxValue);
        assert(i == a.len());
    };
    
    (maxPos as int, maxValue)
}

}