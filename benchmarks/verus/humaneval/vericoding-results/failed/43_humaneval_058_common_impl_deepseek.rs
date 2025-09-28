// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn set_contains_intersection(s1: Set<i32>, s2: Set<i32>) -> (s: Set<i32>)
    ensures
        s == s1.intersect(s2),
        (forall|i: i32| s.contains(i) <==> s1.contains(i) && s2.contains(i))
{
    let s = s1.intersect(s2);
    proof {
        assert(forall|i: i32| s.contains(i) <==> s1.contains(i) && s2.contains(i));
    }
    s
}

/* helper modified by LLM (iteration 5): Fixed insert_seq to insert as advised by compiler */
// </vc-helpers>

// <vc-spec>
fn common(l1: &Vec<i32>, l2: &Vec<i32>) -> (c: Set<i32>)
    ensures 
        (forall|i: i32| c.contains(i) ==> l1@.contains(i) && l2@.contains(i)) &&
        (forall|i: i32| l1@.contains(i) && l2@.contains(i) ==> c.contains(i))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed insert_seq method calls to insert */
    let s1 = Set::empty().insert(l1@);
    let s2 = Set::empty().insert(l2@);
    let c = s1.intersect(s2);
    proof {
        assert forall|i: i32| c.contains(i) implies l1@.contains(i) && l2@.contains(i) by {
            assert(s1.contains(i) && s2.contains(i));
        };
        assert forall|i: i32| l1@.contains(i) && l2@.contains(i) implies c.contains(i) by {
            assert(s1.contains(i) && s2.contains(i));
        };
    }
    c
}
// </vc-code>


}

fn main() {}