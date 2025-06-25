// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(a: Seq<int>) -> bool {
    forall i  0 < i < .len()a| :: a.spec_index(i-1) <= a.spec_index(i)
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
    requires
        a != null && a.len() > 0 && i < a.len() && j < a.len(),
        a != null && a.len() > 0 && lo < a.len()
    ensures
        a.spec_index(i) == old(a.spec_index(j)),
        a.spec_index(j) == old(a.spec_index(i)),
        lo <= minIdx < a.len(),
        forall x :: lo <= x < a.len() ==> a.spec_index(minIdx) <= a.spec_index(x)
{
    return 0;
}

}