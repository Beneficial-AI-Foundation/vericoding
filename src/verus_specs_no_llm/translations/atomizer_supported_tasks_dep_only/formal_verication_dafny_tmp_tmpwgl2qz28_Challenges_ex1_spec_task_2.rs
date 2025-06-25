// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn PalVerify(a: Vec<char>) -> (yn: bool)
    ensures yn == true ==> forall|i: int| 0 <= i < a.len()/2 ==> a[i] == a[a.len() - i -1],
            yn == false ==> exists|i: int| 0 <= i < a.len()/2 and a[i] != a[a.len() - i -1],
            forall|j: int| 0<=j<a.len() ==> a[j] == old(a[j])
{
}

}