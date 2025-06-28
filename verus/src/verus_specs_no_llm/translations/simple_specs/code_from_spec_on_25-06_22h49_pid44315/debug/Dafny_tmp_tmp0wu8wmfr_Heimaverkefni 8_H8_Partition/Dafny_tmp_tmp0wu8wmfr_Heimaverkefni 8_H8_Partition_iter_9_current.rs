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
    let p: int = choose|x: int| multiset_contains(m, x);
    
    // Create the partitions - we'll create post by subtracting one occurrence of p
    let pre = Multiset::<int>::empty();
    let post = m.sub(Multiset::singleton(p));
    
    proof {
        // The choose operator guarantees that multiset_contains(m, p)
        assert(multiset_contains(m, p));
        assert(m.count(p) > 0);
        
        // Now prove m == pre + Multiset::singleton(p) + post
        // Since pre is empty, this becomes m == Multiset::singleton(p) + post
        
        let combined = pre + Multiset::singleton(p) + post;
        
        assert(forall|x: int| combined.count(x) == m.count(x)) by {
            if x == p {
                assert(pre.count(x) == 0);
                assert(Multiset::singleton(p).count(x) == 1);
                assert(post.count(x) == m.sub(Multiset::singleton(p)).count(x));
                assert(post.count(x) == m.count(p) - 1);
                assert(combined.count(x) == 0 + 1 + (m.count(p) - 1));
                assert(combined.count(x) == m.count(p));
            } else {
                assert(pre.count(x) == 0);
                assert(Multiset::singleton(p).count(x) == 0);
                assert(post.count(x) == m.sub(Multiset::singleton(p)).count(x));
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