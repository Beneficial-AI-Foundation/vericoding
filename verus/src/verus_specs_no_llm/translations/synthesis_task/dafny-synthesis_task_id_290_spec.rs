// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_MaxLengthList(lists: Seq<Seq<int>>) -> maxList: seq<int>
    requires
        lists.len() > 0
    ensures
        forall |l: int| l in lists ==> l.len() <= maxList.len(),
        maxList in lists
;

proof fn lemma_MaxLengthList(lists: Seq<Seq<int>>) -> (maxList: Seq<int>)
    requires
        lists.len() > 0
    ensures
        forall |l: int| l in lists ==> l.len() <= maxList.len(),
        maxList in lists
{
    Seq::empty()
}

}