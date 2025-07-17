// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_GetFirstElements(lst: Seq<Seq<int>>) -> result: seq<int>
    requires
        forall |i: int| 0 <= i < lst.len() ==> lst.index(i).len() > 0
    ensures
        result.len() == lst.len(),
        forall |i: int| 0 <= i < result.len() ==> result.index(i) == lst.index(i)[0]
;

proof fn lemma_GetFirstElements(lst: Seq<Seq<int>>) -> (result: Seq<int>)
    requires
        forall |i: int| 0 <= i < lst.len() ==> lst.index(i).len() > 0
    ensures
        result.len() == lst.len(),
        forall |i: int| 0 <= i < result.len() ==> result.index(i) == lst.index(i)[0]
{
    Seq::empty()
}

}