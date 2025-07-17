// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_MinOfMultiset(m: multiset<int>) -> min: int
    requires
        m != multiset
;

proof fn lemma_MinOfMultiset(m: multiset<int>) -> (min: int)
    requires
        m != multiset
{
    0
}

}