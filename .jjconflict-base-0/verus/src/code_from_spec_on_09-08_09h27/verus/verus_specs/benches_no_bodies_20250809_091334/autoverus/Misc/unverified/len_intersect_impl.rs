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
    /* code modified by LLM (iteration 1): removed redundant proof block and use direct assertions */
    assert(s1.intersect(s2).subset_of(s1));
    assert(s1.intersect(s2).finite());
}
}