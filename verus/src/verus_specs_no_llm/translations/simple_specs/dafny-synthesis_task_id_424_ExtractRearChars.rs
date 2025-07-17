// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_ExtractRearChars(l: Seq<String>) -> r: seq<char>
    requires
        forall |i: int| 0 <= i < l.len() ==> l.index(i).len() > 0
    ensures
        r.len() == l.len(),
        forall |i: int| 0 <= i < l.len() ==> r.index(i) == l.index(i)[l.index(i).len() - 1]
;

proof fn lemma_ExtractRearChars(l: Seq<String>) -> (r: Seq<char>)
    requires
        forall |i: int| 0 <= i < l.len() ==> l.index(i).len() > 0
    ensures
        r.len() == l.len(),
        forall |i: int| 0 <= i < l.len() ==> r.index(i) == l.index(i)[l.index(i).len() - 1]
{
    Seq::empty()
}

}