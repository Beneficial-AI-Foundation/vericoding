// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Filter(a: Seq<char>, b: set<char>) -> c:set<char>
    ensures
        forall |x: int| x in a && x in b <==> x in c
;

proof fn lemma_Filter(a: Seq<char>, b: set<char>) -> (c: set<char>)
    ensures
        forall |x: int| x in a && x in b <==> x in c
{
    0
}

}