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
    let mut maxValue: int = a.spec_index(0);
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            0 <= maxPos < a.len(),
            maxValue == a.spec_index(maxPos as int),
            forall|j: int| 0 <= j < i ==> a.spec_index(j) <= maxValue,
            exists|j: int| 0 <= j < i && a.spec_index(j) == maxValue,
            1 <= i <= a.len(),
            maxPos < i
    {
        if a.spec_index(i as int) > maxValue {
            maxPos = i;
            maxValue = a.spec_index(i as int);
        }
        i = i + 1;
    }
    
    // After the loop, i == a.len(), so we've processed all elements
    assert(i == a.len());
    assert(forall|j: int| 0 <= j < a.len() ==> a.spec_index(j) <= maxValue);
    assert(exists|j: int| 0 <= j < a.len() && a.spec_index(j) == maxValue);
    
    (maxPos as int, maxValue)
}

}