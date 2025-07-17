// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_DeepCopySeq(s: Seq<int>) -> copy: seq<int>
    ensures
        copy.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==> copy.index(i) == s.index(i)
;

proof fn lemma_DeepCopySeq(s: Seq<int>) -> (copy: Seq<int>)
    ensures
        copy.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==> copy.index(i) == s.index(i)
{
    Seq::empty()
}

}