// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Partition(m: multiset<int>) -> pre: multiset<int>, p: int, post: multiset<int>
    requires m.len() > 0;
    ensures p in m;,
            m == pre+multiset
{
}

}