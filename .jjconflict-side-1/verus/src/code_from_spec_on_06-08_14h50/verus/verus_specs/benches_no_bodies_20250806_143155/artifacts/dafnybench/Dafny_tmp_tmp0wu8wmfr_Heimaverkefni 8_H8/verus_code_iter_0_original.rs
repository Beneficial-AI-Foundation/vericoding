use vstd::prelude::*;
use vstd::multiset::*;

verus! {
    spec fn partition(m: Multiset<int>) -> (Multiset<int>, int, Multiset<int>)
        recommends m.len() > 0
    {
        let p = m.choose();
        let m_prime = m.remove(p);
        let (pre, post) = partition_helper(m_prime, p, Multiset::empty(), Multiset::empty());
        (pre, p, post)
    }

    spec fn partition_helper(m_prime: Multiset<int>, p: int, pre: Multiset<int>, post: Multiset<int>) -> (Multiset<int>, Multiset<int>)
        decreases m_prime.len()
    {
        if m_prime.len() == 0 {
            (pre, post)
        } else {
            let temp = m_prime.choose();
            let m_new = m_prime.remove(temp);
            if temp <= p {
                partition_helper(m_new, p, pre.add(Multiset::singleton(temp)), post)
            } else {
                partition_helper(m_new, p, pre, post.add(Multiset::singleton(temp)))
            }
        }
    }

    spec fn quickselect(m: Multiset<int>, k: nat) -> (Multiset<int>, int, Multiset<int>)
        recommends k < m.len()
        decreases m.len()
    {
        let (pre, kth, post) = partition(m);
        if pre.len() == k {
            (pre, kth, post)
        } else if k > pre.len() {
            let k_new = (k - pre.len() - 1) as nat;
            let (pre_prime, p, post_prime) = quickselect(post, k_new);
            let new_pre = pre.add(Multiset::singleton(kth)).add(pre_prime);
            let new_post = post.sub(pre_prime).sub(Multiset::singleton(p));
            (new_pre, p, new_post)
        } else {
            let (pre_prime, p, post_prime) = quickselect(pre, k);
            let new_pre = pre.sub(Multiset::singleton(p)).sub(post_prime);
            let new_post = post.add(Multiset::singleton(kth)).add(post_prime);
            (new_pre, p, new_post)
        }
    }

    fn main() {}
}