// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_LucidNumbers(n: int) -> lucid: seq<int>
    requires
        n >= 0
    ensures
        forall |i: int| 0 <= i < lucid.len() ==> lucid.index(i) % 3 == 0,
        forall |i: int| 0 <= i < lucid.len() ==> lucid.index(i) <= n,
        forall |i: int, j: int| 0 <= i < j < lucid.len() ==> lucid.index(i) < lucid.index(j)
;

proof fn lemma_LucidNumbers(n: int) -> (lucid: Seq<int>)
    requires
        n >= 0
    ensures
        forall |i: int| 0 <= i < lucid.len() ==> lucid.index(i) % 3 == 0,
        forall |i: int| 0 <= i < lucid.len() ==> lucid.index(i) <= n,
        forall |i: int, j: int| 0 <= i < j < lucid.len() ==> lucid.index(i) < lucid.index(j)
{
    Seq::empty()
}

}