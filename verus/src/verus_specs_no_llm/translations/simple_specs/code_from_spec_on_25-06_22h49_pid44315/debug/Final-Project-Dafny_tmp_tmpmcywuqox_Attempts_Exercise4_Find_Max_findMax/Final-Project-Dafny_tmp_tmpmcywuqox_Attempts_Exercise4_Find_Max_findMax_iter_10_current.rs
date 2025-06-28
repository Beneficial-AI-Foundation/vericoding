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
            maxValue >= 0,
            maxPos < i
    {
        if a[i] > maxValue {
            maxPos = i;
            maxValue = a[i];
            
            // Proof that the new maxValue is still >= 0
            assert(maxValue >= 0);
            
            // Proof that all previous elements are still <= new maxValue
            assert(forall|j: int| 0 <= j < i ==> a.spec_index(j) <= maxValue) by {
                let old_max = old(maxValue);
                assert(forall|j: int| 0 <= j < i ==> a.spec_index(j) <= old_max);
                assert(old_max < maxValue);
            };
        }
        
        // Proof that the invariant is maintained for the extended range
        assert(forall|j: int| 0 <= j < (i + 1) ==> a.spec_index(j) <= maxValue) by {
            assert(forall|j: int| 0 <= j < i ==> a.spec_index(j) <= maxValue);
            assert(a.spec_index(i as int) <= maxValue);
        };
        
        assert(exists|j: int| 0 <= j < (i + 1) && a.spec_index(j) == maxValue) by {
            assert(a.spec_index(maxPos as int) == maxValue);
            assert(0 <= maxPos < (i + 1));
        };
        
        i = i + 1;
    }
    
    // Final proofs for postconditions
    assert(i == a.len());
    assert(forall|j: int| 0 <= j < a.len() ==> a.spec_index(j) <= maxValue);
    assert(exists|j: int| 0 <= j < a.len() && a.spec_index(j) == maxValue) by {
        assert(a.spec_index(maxPos as int) == maxValue);
        assert(0 <= maxPos < a.len());
    };
    
    (maxPos as int, maxValue)
}

}