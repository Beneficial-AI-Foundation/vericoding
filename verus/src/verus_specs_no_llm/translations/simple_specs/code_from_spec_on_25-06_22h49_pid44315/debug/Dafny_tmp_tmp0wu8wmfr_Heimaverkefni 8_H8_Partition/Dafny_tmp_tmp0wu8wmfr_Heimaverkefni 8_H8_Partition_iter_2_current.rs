use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Partition(m: Multiset<int>) -> (pre: Multiset<int>, p: int, post: Multiset<int>)
    requires
        m.len() > 0
    ensures
        m.contains(p),
        m == pre + Multiset::singleton(p) + post
{
    // Choose an arbitrary element from the multiset as pivot
    let p = m.choose();
    
    // Create the remaining multiset after removing one instance of p
    let remaining = m.remove(p);
    
    // For simplicity, we can put all remaining elements in post
    // making pre empty
    let pre = Multiset::<int>::empty();
    let post = remaining;
    
    // The postconditions are satisfied by the properties of choose() and remove()
    assert(m.contains(p));  // choose() guarantees this
    assert(m == remaining + Multiset::singleton(p));  // remove() guarantees this
    assert(m == pre + Multiset::singleton(p) + post);  // by substitution
    
    (pre, p, post)
}

}