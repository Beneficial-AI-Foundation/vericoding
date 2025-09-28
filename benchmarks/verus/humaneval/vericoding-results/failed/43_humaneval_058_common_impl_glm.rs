// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): empty helper section */
// </vc-helpers>

// <vc-spec>
fn common(l1: &Vec<i32>, l2: &Vec<i32>) -> (c: Set<i32>)
    ensures 
        (forall|i: i32| c.contains(i) ==> l1@.contains(i) && l2@.contains(i)) &&
        (forall|i: i32| l1@.contains(i) && l2@.contains(i) ==> c.contains(i))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed Set::empty call with proper mode */
{
    let mut c = Set::empty();
    for i in 0..l1.len()
        invariant
            forall|j: i32| c.contains(j) ==> l1@.contains(j) && l2@.contains(j),
            forall|j: i32| l1@.contains(j) && l2@.contains(j) && l1@.index_of(j) < i ==> c.contains(j),
    {
        let val = l1[i];
        if l2@.contains(val) {
            c.insert(val);
        }
    }
    c
}
// </vc-code>


}

fn main() {}