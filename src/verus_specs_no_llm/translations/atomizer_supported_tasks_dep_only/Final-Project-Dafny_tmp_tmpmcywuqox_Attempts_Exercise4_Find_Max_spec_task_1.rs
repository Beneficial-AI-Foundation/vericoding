// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn findMax(a: Vec<int>) -> (pos: int, maxVal: int)
    requires
        a.len() > 0;,
        forall i :: 0 <= i < a.len() ==> a.spec_index(i) >= 0;
    ensures
        forall i :: 0 <= i < a.len() ==> a.spec_index(i) <= maxVal;,
        exists i :: 0 <= i < a.len() &&  a.spec_index(i) == maxVal;,
        0 <= pos < a.len(),
        a.spec_index(pos) == maxVal;
{
    return (0, 0);
}

}