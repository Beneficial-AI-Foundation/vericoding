// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_msetEqual(s: multiset<char>, t: multiset<char>) -> equal: bool
    ensures
        s == t <==> equal
;

proof fn lemma_msetEqual(s: multiset<char>, t: multiset<char>) -> (equal: bool)
    ensures
        s == t <==> equal
{
    false
}

}