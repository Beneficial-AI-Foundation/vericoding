// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn findMax(a: Vec<int>) -> pos: int, maxVal: int
    requires a.len() > 0;,
             forall|i: int| 0 <= i < a.len() ==> a[i] >= 0;
    ensures forall|i: int| 0 <= i < a.len() ==> a[i] <= maxVal;,
            exists|i: int| 0 <= i < a.len() and  a[i] == maxVal;,
            0 <= pos < a.len(),
            a[pos] == maxVal;
{
}

}