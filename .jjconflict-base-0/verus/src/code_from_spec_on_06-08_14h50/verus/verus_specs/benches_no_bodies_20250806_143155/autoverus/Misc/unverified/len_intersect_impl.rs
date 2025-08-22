//an example from Verus tutorial. VERY difficult.

use vstd::prelude::*;
fn main() {}

verus!{
     
pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        s1.intersect(s2).len() <= s1.len(),
    decreases
        s1.len(),
{
    // The intersection of s1 and s2 is a subset of s1
    // Since s1 is finite, the intersection is also finite
    // and its length is at most the length of s1
    assert(s1.intersect(s2).subset_of(s1));
}
}