// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_MinLengthSublist(s: Seq<Seq<int>>) -> minSublist: seq<int>
    requires
        s.len() > 0
    ensures
        minSublist in s,
        forall |sublist: int| sublist in s ==> minSublist.len() <= sublist.len()
;

proof fn lemma_MinLengthSublist(s: Seq<Seq<int>>) -> (minSublist: Seq<int>)
    requires
        s.len() > 0
    ensures
        minSublist in s,
        forall |sublist: int| sublist in s ==> minSublist.len() <= sublist.len()
{
    Seq::empty()
}

}