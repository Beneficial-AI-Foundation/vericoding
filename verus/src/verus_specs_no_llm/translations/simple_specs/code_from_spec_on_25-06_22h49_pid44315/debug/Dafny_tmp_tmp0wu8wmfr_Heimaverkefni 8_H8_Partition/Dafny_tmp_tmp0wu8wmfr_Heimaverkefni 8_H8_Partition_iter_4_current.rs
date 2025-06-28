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
    // We'll use a proof-by-construction approach
    proof {
        // Since m.len() > 0, there exists at least one element with count > 0
        assert(exists|x: int| m.count(x) > 0);
    }
    
    // Choose an element that we know exists in the multiset
    let p: int = choose|x: int| m.count(x) > 0;
    
    // Create the partitions
    let pre = Multiset::<int>::empty();
    let post = m.remove(p);
    
    // Verify the postconditions
    assert(multiset_contains(m, p));
    
    proof {
        // Prove m == pre + Multiset::singleton(p) + post
        assert(pre.len() == 0);
        assert(post == m.remove(p));
        
        // Key insight: for any multiset m and element p where m.count(p) > 0,
        // we have m == m.remove(p) + Multiset::singleton(p)
        assert(forall|x: int| 
            if x == p {
                (post + Multiset::singleton(p)).count(x) == post.count(x) + 1 == (m.count(p) - 1) + 1 == m.count(p)
            } else {
                (post + Multiset::singleton(p)).count(x) == post.count(x) + 0 == m.count(x)
            }
        );
        
        // Therefore m == post + Multiset::singleton(p)
        assert(m =~= post + Multiset::singleton(p));
        
        // Since pre is empty: pre + Multiset::singleton(p) + post == Multiset::singleton(p) + post
        assert(pre + Multiset::singleton(p) + post =~= Multiset::singleton(p) + post);
        
        // And Multiset::singleton(p) + post == post + Multiset::singleton(p) (commutativity)
        assert(Multiset::singleton(p) + post =~= post + Multiset::singleton(p));
        
        // Therefore the final equality holds
        assert(m =~= pre + Multiset::singleton(p) + post);
    }
    
    (pre, p, post)
}

}