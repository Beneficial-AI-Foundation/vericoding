use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Partition(m: multiset<int>) -> (pre: multiset<int>, p: int, post: multiset<int>)
    requires
        m.len() > 0
    ensures
        p in m,
        m == pre + multiset{p} + post
{
    // Choose an arbitrary element from the multiset as pivot
    let p = m.choose();
    
    // Create the remaining multiset after removing one instance of p
    let remaining = m.remove(p);
    
    // For simplicity, we can put all remaining elements in either pre or post
    // Here we put them all in post, making pre empty
    let pre = multiset::<int>::empty();
    let post = remaining;
    
    (pre, p, post)
}

}