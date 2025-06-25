// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Reverse(a: Vec<char>) -> (b: Vec<char>)
    requires a.len() > 0
    ensures a.len() == b.len(),
            forall|x: int| 0 <= x < a.len() ==> b[x] == a[a.len() - x - 1]
{
}

}