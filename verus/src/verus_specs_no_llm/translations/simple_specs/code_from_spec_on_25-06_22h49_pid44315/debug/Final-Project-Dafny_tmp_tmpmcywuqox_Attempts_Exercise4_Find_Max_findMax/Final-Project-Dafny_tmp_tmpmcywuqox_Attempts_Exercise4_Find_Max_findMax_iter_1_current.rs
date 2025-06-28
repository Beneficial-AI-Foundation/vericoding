use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn findMax(a: Vec<int>) -> (pos: int, maxVal: int)
    requires
        a.len() > 0,
        forall i :: 0 <= i < a.len() ==> a.spec_index(i) >= 0
    ensures
        forall i :: 0 <= i < a.len() ==> a.spec_index(i) <= maxVal,
        exists i :: 0 <= i < a.len() && a.spec_index(i) == maxVal,
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
            forall j :: 0 <= j < i ==> a.spec_index(j) <= maxValue,
            exists j :: 0 <= j < i && a.spec_index(j) == maxValue,
            1 <= i <= a.len()
    {
        if a[i] > maxValue {
            maxPos = i;
            maxValue = a[i];
        }
        i = i + 1;
    }
    
    (maxPos as int, maxValue)
}

}