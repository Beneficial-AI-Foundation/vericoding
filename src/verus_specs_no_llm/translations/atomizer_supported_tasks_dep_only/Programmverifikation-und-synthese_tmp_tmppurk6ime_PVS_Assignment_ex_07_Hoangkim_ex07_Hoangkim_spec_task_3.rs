// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn sorted(a: Seq<int>) -> bool {
    forall|i  0 < i < .len()a|: int| a[i-1] <= a[i]
}

fn swap(a: Vec<int>, i: nat, j: nat)
    modifies a
    requires a != null && a.Length > 0 && i < a.Length && j < a.Length
    ensures a[i] == old(a[j])
    ensures a[j] == old(a[i])
{
}


//b)
//Problem04
// SPEC 

//b)
//Problem04
method FindMin(a: array<int>, lo: nat) -> (minIdx: nat)
    requires a != null and a.len() > 0 and i < a.len() and j < a.len(),
             a != null and a.len() > 0 and lo < a.len()
    ensures a[i] == old(a[j]),
            a[j] == old(a[i]),
            lo <= minIdx < a.len(),
            forall|x: int| lo <= x < a.len() ==> a[minIdx] <= a[x]
{
}

}