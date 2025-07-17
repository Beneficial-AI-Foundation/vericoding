// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn total(a: Seq<nat>) -> nat
{
    0
}

spec fn spec_Total(a: Seq<nat>) -> r:nat
    ensures
        r == total (a.index(0..a.len()))
;

proof fn lemma_Total(a: Seq<nat>) -> (r: nat)
    ensures
        r == total (a.index(0..a.len()))
{
    0
}

}