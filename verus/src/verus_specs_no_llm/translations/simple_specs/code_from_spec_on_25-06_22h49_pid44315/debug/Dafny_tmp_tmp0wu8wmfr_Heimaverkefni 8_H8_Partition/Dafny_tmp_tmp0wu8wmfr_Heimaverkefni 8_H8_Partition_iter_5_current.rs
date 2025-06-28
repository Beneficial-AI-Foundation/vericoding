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
    let post = m.remove(p);
    
    proof {
        // First, establish that p is in m
        assert(m.count(p) > 0);
        assert(multiset_contains(m, p));
        
        // Now prove m == pre + Multiset::singleton(p) + post
        // Since pre is empty, this becomes m == Multiset::singleton(p) + post
        
        // For the remove operation, we know that:
        // m.remove(p).count(p) == m.count(p) - 1
        // m.remove(p).count(x) == m.count(x) for x != p
        
        assert(post.count(p) == m.count(p) - 1);
        assert(forall|x: int| x != p ==> post.count(x) == m.count(x));
        
        // Now check that pre + Multiset::singleton(p) + post == m
        let combined = pre + Multiset::singleton(p) + post;
        
        assert(forall|x: int| {
            if x == p {
                combined.count(x) == pre.count(x) + Multiset::singleton(p).count(x) + post.count(x)
                    == 0 + 1 + (m.count(p) - 1)
                    == m.count(p)
            } else {
                combined.count(x) == pre.count(x) + Multiset::singleton(p).count(x) + post.count(x)
                    == 0 + 0 + m.count(x)
                    == m.count(x)
            }
        });
        
        // Since counts are equal for all elements, the multisets are equal
        assert(m == combined);
    }
    
    (pre, p, post)
}

}