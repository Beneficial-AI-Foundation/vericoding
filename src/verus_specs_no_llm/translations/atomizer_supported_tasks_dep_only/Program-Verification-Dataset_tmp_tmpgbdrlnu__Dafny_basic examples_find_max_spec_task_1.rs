// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn FindMax(a: Vec<int>) -> (max: int)
    requires a != null and a.len() > 0;
    ensures 0 <= max < a.len();,
            forall|x: int| 0 <= x < a.len() ==> a[max] >= a[x];
{
}

}