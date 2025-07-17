// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Partition(m: multiset<int>) -> pre: multiset<int>, p: int, post: multiset<int>
    requires
        m.len() > 0
    ensures
        p in m,
        m == pre+multiset
;

proof fn lemma_Partition(m: multiset<int>) -> (pre: multiset<int>, p: int, post: multiset<int>)
    requires
        m.len() > 0
    ensures
        p in m,
        m == pre+multiset
{
    (0, 0, 0)
}

}