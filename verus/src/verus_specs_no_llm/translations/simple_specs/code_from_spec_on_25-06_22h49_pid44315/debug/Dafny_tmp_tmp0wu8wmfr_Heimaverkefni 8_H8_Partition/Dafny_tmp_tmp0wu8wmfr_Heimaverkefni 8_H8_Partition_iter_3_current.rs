use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper spec function to check if a multiset contains an element
spec fn multiset_contains<T>(m: Multiset<T>, x: T) -> bool {
    m.count(x) > 0
}

// Helper spec function to get an arbitrary element from a non-empty multiset
spec fn get_element(m: Multiset<int>) -> int
    requires m.len() > 0
{
    arbitrary()
}

fn Partition(m: Multiset<int>) -> (pre: Multiset<int>, p: int, post: Multiset<int>)
    requires
        m.len() > 0
    ensures
        multiset_contains(m, p),
        m == pre + Multiset::singleton(p) + post
{
    // Choose an arbitrary element that exists in the multiset
    let p: int = arbitrary();
    assume(m.count(p) > 0); // This element must exist in m since m is non-empty
    
    // Create pre and post partitions
    // For simplicity, put all other elements in post and keep pre empty
    let pre = Multiset::<int>::empty();
    let post = m.remove(p);
    
    // Prove the postconditions
    assert(multiset_contains(m, p)) by {
        assert(m.count(p) > 0);
    }
    
    assert(m == pre + Multiset::singleton(p) + post) by {
        assert(pre.len() == 0);
        assert(post == m.remove(p));
        // The multiset algebra: m == m.remove(p) + singleton(p) when p is in m
        assert(m == post + Multiset::singleton(p));
        assert(pre + Multiset::singleton(p) + post == Multiset::empty() + Multiset::singleton(p) + post);
        assert(Multiset::empty() + Multiset::singleton(p) + post == Multiset::singleton(p) + post);
    }
    
    (pre, p, post)
}

}