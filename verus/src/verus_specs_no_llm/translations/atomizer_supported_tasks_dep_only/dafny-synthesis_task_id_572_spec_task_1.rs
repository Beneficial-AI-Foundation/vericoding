// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_RemoveDuplicates(a: Vec<int>) -> result: seq<int>
    requires
        a != null
    ensures
        forall |x: int| x in result <==> exists |i: int| 0 <= i < a.len() && a.index(i) == x,
        forall |i: int, j: int| 0 <= i < j < result.len() ==> result.index(i) != result.index(j)
;

proof fn lemma_RemoveDuplicates(a: Vec<int>) -> (result: Seq<int>)
    requires
        a != null
    ensures
        forall |x: int| x in result <==> exists |i: int| 0 <= i < a.len() && a.index(i) == x,
        forall |i: int, j: int| 0 <= i < j < result.len() ==> result.index(i) != result.index(j)
{
    Seq::empty()
}

}