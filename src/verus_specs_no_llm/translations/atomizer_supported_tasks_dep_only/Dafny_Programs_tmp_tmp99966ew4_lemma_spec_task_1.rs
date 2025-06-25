// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn FindZero(a: Vec<int>) -> (index: int)
    requires a != null,
             forall|i: int| 0 <= i < a.len() ==> 0 <= a[i],
             forall|i: int| 0 < i < a.len() ==> a[i-1]-1 <= a[i]
    ensures index < 0  ==> forall|i: int| 0 <= i < a.len() ==> a[i] != 0,
            0 <= index ==> index < a.len() and a[index] == 0
{
}

}