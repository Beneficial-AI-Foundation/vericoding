// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn firste(a: Vec<char>) -> (c: int)
    ensures -1 <= c < a.len(),
            0 <= c < a.len() ==> a[c] == 'e' and forall|x: int| 0 <= x < c ==> a[x] != 'e',
            c == -1 ==> forall|x: int| 0 <= x < a.len() ==> a[x] != 'e'
{
}

}