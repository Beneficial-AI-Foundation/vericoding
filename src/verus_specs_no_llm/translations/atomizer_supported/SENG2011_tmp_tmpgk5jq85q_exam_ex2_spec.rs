// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Getmini(a: Vec<int>) -> (mini: nat)
    requires a.len() > 0
    ensures 0 <= mini < a.len() // mini is an index of a,
            forall|x: int| 0 <= x < a.len() ==> a[mini] <= a[x] // a[mini] is the minimum value,
            forall|x: int| 0 <= x < mini ==> a[mini] < a[x] // a[mini] is the first min
{
}

}