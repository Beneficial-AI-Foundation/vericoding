// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec set defining intersection of two sequences */
spec fn intersection(s1: Seq<i32>, s2: Seq<i32>) -> Set<i32> {
    Set::new(|i: i32| s1.contains(i) && s2.contains(i))
}
// </vc-helpers>

// <vc-spec>
fn common(l1: &Vec<i32>, l2: &Vec<i32>) -> (c: Set<i32>)
    ensures 
        (forall|i: i32| c.contains(i) ==> l1@.contains(i) && l2@.contains(i)) &&
        (forall|i: i32| l1@.contains(i) && l2@.contains(i) ==> c.contains(i))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct the intersection set as a ghost value and return it */
    let ghost c = intersection(l1@, l2@);
    c
}
// </vc-code>


}

fn main() {}