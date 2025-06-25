// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn aba(a: Vec<int>) -> (b: Vec<int>)
    ensures a.len() == b.len() // needed for next line,
            forall|x: int| 0<=x<b.len() ==> b[x] == abs(a[x])
{
}

}