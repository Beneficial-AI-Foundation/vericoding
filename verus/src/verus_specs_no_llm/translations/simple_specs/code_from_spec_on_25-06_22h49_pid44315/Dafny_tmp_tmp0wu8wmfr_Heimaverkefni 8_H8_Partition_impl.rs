use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper spec function to check if a multiset contains an element
spec fn multiset_contains<T>(m: Multiset<T>, x: T) -> bool {
    m.count(x) > 0
}

fn Partition(m: Multiset<int>) -> (pre: Multiset<int>, p: int, post: Multiset<int>)
    requires
        m.len() > 0
    ensures
        multiset_contains(m, p),
        m == pre + Multiset::singleton(p) + post
{
    // Since m is non-empty, we can choose any element from it
    // We'll use choose to get an element that exists in the multiset
    let p: int = choose|x: int| m.count(x) > 0;
    
    // Create the partitions
    let pre = Multiset::<int>::empty();
    // Create post by removing one occurrence of p from m
    let singleton_p = Multiset::singleton(p);
    let post = m - singleton_p;
    
    proof {
        // The choose operator guarantees that m.count(p) > 0
        assert(m.count(p) > 0);
        assert(multiset_contains(m, p));
        
        // Now prove m == pre + Multiset::singleton(p) + post
        // Since pre is empty, this becomes m == Multiset::singleton(p) + post
        
        let combined = pre + singleton_p + post;
        
        // Prove that the combined multiset equals the original
        assert forall|x: int| combined.count(x) == m.count(x) by {
            if x == p {
                assert(pre.count(x) == 0);
                assert(singleton_p.count(x) == 1);
                assert(post.count(x) == (m - singleton_p).count(x));
                // For subtraction: (m - singleton_p).count(x) = m.count(x) - singleton_p.count(x)
                // when m.count(x) >= singleton_p.count(x)
                assert(post.count(x) == m.count(x) - 1);
                assert(combined.count(x) == 0 + 1 + (m.count(x) - 1));
                assert(combined.count(x) == m.count(x));
            } else {
                assert(pre.count(x) == 0);
                assert(singleton_p.count(x) == 0);
                assert(post.count(x) == (m - singleton_p).count(x));
                // For x != p, singleton_p.count(x) == 0, so subtraction doesn't change count
                assert(post.count(x) == m.count(x));
                assert(combined.count(x) == 0 + 0 + m.count(x));
                assert(combined.count(x) == m.count(x));
            }
        };
        
        // Since counts are equal for all elements, the multisets are equal
        assert(m == combined);
    }
    
    (pre, p, post)
}

}