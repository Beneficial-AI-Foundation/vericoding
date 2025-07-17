// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_toMultiset(s: String) -> mset: multiset<char>
    ensures
        multiset(s) == mset
;

proof fn lemma_toMultiset(s: String) -> (mset: multiset<char>)
    ensures
        multiset(s) == mset
{
    0
}

}