// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_findMin(a: Vec<real>, from: nat, to: nat) -> index: nat
    requires
        0 <= from < to <= a.len()
    ensures
        from <= index < to,
        forall |k: int| from <= k < to ==> a.index(k) >= a.index(index)
;

proof fn lemma_findMin(a: Vec<real>, from: nat, to: nat) -> (index: nat)
    requires
        0 <= from < to <= a.len()
    ensures
        from <= index < to,
        forall |k: int| from <= k < to ==> a.index(k) >= a.index(index)
{
    0
}

}