use vstd::prelude::*;

verus! {

pub fn Partition(m: Multiset<int>) -> (pre: Multiset<int>, p: int, post: Multiset<int>)
    requires(m.len() > 0)
    ensures(m == pre + Multiset::singleton(p) + post)
    ensures(forall|z: int| pre.count(z) > 0 ==> z <= p)
    ensures(forall|z: int| post.count(z) > 0 ==> z >= p)
{
    unimplemented!()
}

pub fn QuickSelect(m: Multiset<int>, k: int) -> (pre: Multiset<int>, kth: int, post: Multiset<int>)
    requires(0 <= k < m.len())
    ensures(m.count(kth) > 0)
    ensures(m == pre + Multiset::singleton(kth) + post)
    ensures(pre.len() == k)
    ensures(forall|z: int| pre.count(z) > 0 ==> z <= kth)
    ensures(forall|z: int| post.count(z) > 0 ==> z >= kth)
{
    unimplemented!()
}

}