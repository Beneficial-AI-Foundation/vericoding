// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn buscar(a: Vec<int>, x: int) -> (r: int)
    ensures r < 0 ==> forall|i: int| 0 <= i <a.len() ==> a[i] != x,
            0 <= r < a.len() ==> a[r] == x
{
}

}