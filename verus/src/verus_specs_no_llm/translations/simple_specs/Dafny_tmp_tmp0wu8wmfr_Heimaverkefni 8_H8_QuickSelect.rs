// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_QuickSelect(m: multiset<int>, k: int) -> pre: multiset<int>, kth: int, post: multiset<int>
    requires
        0 <= k < m.len()
    ensures
        kth in m,
        m == pre+multiset
;

proof fn lemma_QuickSelect(m: multiset<int>, k: int) -> (pre: multiset<int>, kth: int, post: multiset<int>)
    requires
        0 <= k < m.len()
    ensures
        kth in m,
        m == pre+multiset
{
    (0, 0, 0)
}

}