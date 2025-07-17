// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(a: Seq<int>) -> bool {
    forall i  0 < i < .len()a| :: a.index(i-1) <= a.index(i)
}

spec fn spec_swap(a: Vec<int>, i: nat, j: nat)
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
method FindMin(a: array<int>, lo: nat) -> minIdx: nat
    requires
        a != null && a.len() > 0 && i < a.len() && j < a.len(),
        a != null && a.len() > 0 && lo < a.len()
    ensures
        a.index(i) == old(a.index(j)),
        a.index(j) == old(a.index(i)),
        lo <= minIdx < a.len(),
        forall |x: int| lo <= x < a.len() ==> a.index(minIdx) <= a.index(x)
;

proof fn lemma_swap(a: Vec<int>, i: nat, j: nat)
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
        a.index(i) == old(a.index(j)),
        a.index(j) == old(a.index(i)),
        lo <= minIdx < a.len(),
        forall |x: int| lo <= x < a.len() ==> a.index(minIdx) <= a.index(x)
{
    0
}

}