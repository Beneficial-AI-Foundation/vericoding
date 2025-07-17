// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_IsSmaller(a: Seq<int>, b: Seq<int>) -> result: bool
    requires
        a.len() == b.len()
    ensures
        result <==> forall |i: int| 0 <= i < a.len() ==> a.index(i) > b.index(i),
        !result <==> exists |i: int| 0 <= i < a.len() && a.index(i) <= b.index(i)
;

proof fn lemma_IsSmaller(a: Seq<int>, b: Seq<int>) -> (result: bool)
    requires
        a.len() == b.len()
    ensures
        result <==> forall |i: int| 0 <= i < a.len() ==> a.index(i) > b.index(i),
        !result <==> exists |i: int| 0 <= i < a.len() && a.index(i) <= b.index(i)
{
    false
}

}