// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn QuickSelect(m: multiset<int>, k: int) -> pre: multiset<int>, kth: int, post: multiset<int>
    requires 0 <= k < m.len();
    ensures kth in m;,
            m == pre+multiset
{
}

}