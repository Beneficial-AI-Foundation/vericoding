// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Find(a: Vec<int>, key: int) -> (index: int)
    ensures -1<=index<a.len(),
            index!=-1 ==> a[index]==key and (forall|i: int| 0 <= i < index ==> a[i] != key),
            index == -1 ==> (forall|i: int|0 <= i < a.len() ==> a[i] != key)
{
}

}