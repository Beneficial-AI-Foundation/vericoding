// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn CubeElements(a: Vec<int>) -> (cubed: Vec<int>)
    ensures cubed.len() == a.len(),
            forall|i: int| 0 <= i < a.len() ==> cubed[i] == a[i] * a[i] * a[i]
{
}

}