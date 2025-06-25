// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn IsGreater(n: int, a: Vec<int>) -> (result: bool)
    requires a != null
    ensures result ==> forall|i: int| 0 <= i < a.len() ==> n > a[i],
            !result ==> exists|i: int| 0 <= i < a.len() and n <= a[i]
{
}

}