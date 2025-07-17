// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Getmini(a: Vec<int>) -> mini:nat
    requires
        a.len() > 0
    ensures
        0 <= mini < a.len() // mini is an index of a,
        forall |x: int| 0 <= x < a.len() ==> a.index(mini) <= a.index(x) // a.index(mini) is the minimum value,
        forall |x: int| 0 <= x < mini ==> a.index(mini) < a.index(x) // a.index(mini) is the first min
;

proof fn lemma_Getmini(a: Vec<int>) -> (mini: nat)
    requires
        a.len() > 0
    ensures
        0 <= mini < a.len() // mini is an index of a,
        forall |x: int| 0 <= x < a.len() ==> a.index(mini) <= a.index(x) // a.index(mini) is the minimum value,
        forall |x: int| 0 <= x < mini ==> a.index(mini) < a.index(x) // a.index(mini) is the first min
{
    0
}

}