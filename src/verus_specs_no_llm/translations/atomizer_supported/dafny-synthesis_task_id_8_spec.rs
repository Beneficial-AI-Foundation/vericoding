// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn SquareElements(a: Vec<int>) -> (squared: Vec<int>)
    ensures squared.len() == a.len(),
            forall|i: int| 0 <= i < a.len() ==> squared[i] == a[i] * a[i]
{
}

}