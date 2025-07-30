
use vstd::prelude::*;

verus!{
     
proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
    // pre-conditions-start
    requires
        s1.finite(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        s1.intersect(s2).len() <= s1.len(),
    decreases
        s1.len(),
    // post-conditions-end
{
    // impl-start
    if s1.is_empty() {
        assert(s1.intersect(s2).len() == 0) by {
            assert(s1.intersect(s2) =~= s1);
        }
    } else {
        let a = s1.choose();
        lemma_len_intersect(s1.remove(a), s2);
        
        assert(s1.intersect(s2).remove(a).len() <= s1.remove(a).len()) by {
            assert(s1.intersect(s2).remove(a) =~= s1.remove(a).intersect(s2));
        }
    }
    // impl-end
}
// pure-end
}

fn main() {}
