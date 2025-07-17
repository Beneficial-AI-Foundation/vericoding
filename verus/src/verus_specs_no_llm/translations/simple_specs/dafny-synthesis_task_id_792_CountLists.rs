// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_CountLists(lists: Seq<Seq<int>>) -> count: int
    ensures
        count >= 0,
        count == lists.len()
;

proof fn lemma_CountLists(lists: Seq<Seq<int>>) -> (count: int)
    ensures
        count >= 0,
        count == lists.len()
{
    0
}

}