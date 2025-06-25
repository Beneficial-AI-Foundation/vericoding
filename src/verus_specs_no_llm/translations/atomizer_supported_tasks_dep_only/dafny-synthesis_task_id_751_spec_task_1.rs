// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn IsMinHeap(a: Vec<int>) -> (result: bool)
    requires a != null
    ensures result ==> forall|i: int| 0 <= i < a.len() / 2 ==> a[i] <= a[2*i + 1] and (2*i + 2 == a.len() or a[i] <= a[2*i + 2]),
            !result ==> exists|i: int| 0 <= i < a.len() / 2 and (a[i] > a[2*i + 1] or (2*i + 2 != a.len() and a[i] > a[2*i + 2]))
{
}

}