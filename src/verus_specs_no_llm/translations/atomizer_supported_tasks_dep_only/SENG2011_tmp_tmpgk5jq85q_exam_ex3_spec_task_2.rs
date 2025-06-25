// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Symmetric(a: Vec<int>) -> (flag: bool)
    ensures flag == true ==> forall|x: int| 0 <= x < a.len() ==> a[x] == a[a.len() - x - 1],
            flag == false ==> exists|x: int| 0 <= x < a.len() and a[x] != a[a.len() - x - 1]
{
}

}