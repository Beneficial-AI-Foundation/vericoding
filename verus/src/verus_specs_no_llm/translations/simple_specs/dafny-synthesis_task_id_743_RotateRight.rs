// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_RotateRight(l: Seq<int>, n: int) -> r: seq<int>
    requires
        n >= 0
    ensures
        r.len() == l.len(),
        forall |i: int| 0 <= i < l.len() ==> r.index(i) == l.index((i - n + l.len()) % l.len())
;

proof fn lemma_RotateRight(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires
        n >= 0
    ensures
        r.len() == l.len(),
        forall |i: int| 0 <= i < l.len() ==> r.index(i) == l.index((i - n + l.len()) % l.len())
{
    Seq::empty()
}

}