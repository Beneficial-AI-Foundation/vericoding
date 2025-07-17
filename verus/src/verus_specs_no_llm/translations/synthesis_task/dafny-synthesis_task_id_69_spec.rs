// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_ContainsSequence(list: Seq<Seq<int>>, sub: Seq<int>) -> result: bool
    ensures
        result <==> (exists |i: int| 0 <= i < list.len() && sub == list.index(i))
;

proof fn lemma_ContainsSequence(list: Seq<Seq<int>>, sub: Seq<int>) -> (result: bool)
    ensures
        result <==> (exists |i: int| 0 <= i < list.len() && sub == list.index(i))
{
    false
}

}