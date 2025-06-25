pub fn Partition(m: Multiset<int>) -> (pre: Multiset<int>, p: int, post: Multiset<int>)
    requires(m.len() > 0)
    ensures(m.contains(p))
    ensures(m == pre + Multiset::singleton(p) + post)
    ensures(forall|z: int| pre.contains(z) ==> z <= p)
    ensures(forall|z: int| post.contains(z) ==> z >= p)
{
}

pub fn QuickSelect(m: Multiset<int>, k: int) -> (pre: Multiset<int>, kth: int, post: Multiset<int>)
    requires(0 <= k < m.len())
    ensures(m.contains(kth))
    ensures(m == pre + Multiset::singleton(kth) + post)
    ensures(pre.len() == k)
    ensures(forall|z: int| pre.contains(z) ==> z <= kth)
    ensures(forall|z: int| post.contains(z) ==> z >= kth)
{
}