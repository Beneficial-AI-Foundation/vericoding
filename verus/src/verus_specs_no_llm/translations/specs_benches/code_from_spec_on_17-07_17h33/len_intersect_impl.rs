use vstd::prelude::*;
fn main() {}

verus!{
     
//IMPL lemma_len_intersect
pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        s1.intersect(s2).len() <= s1.len(),
    decreases
        s1.len(),
{
    /* code modified by LLM (iteration 4): use direct cardinality argument with intersection definition */
    
    // The intersection is finite since s1 is finite
    assert(s1.intersect(s2).finite());
    
    // Use the fact that intersection cardinality is bounded by constituent set cardinalities
    // This is a fundamental property: |A ∩ B| ≤ |A| and |A ∩ B| ≤ |B|
    assert(s1.intersect(s2).len() <= s1.len()) by {
        // The intersection contains only elements that are in both s1 and s2
        // Therefore, it contains at most as many elements as s1
        assert forall |x: A| s1.intersect(s2).contains(x) implies s1.contains(x) by {
            // By definition of intersection
        }
    }
}
}