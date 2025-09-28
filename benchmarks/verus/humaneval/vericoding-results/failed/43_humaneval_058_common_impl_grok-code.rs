// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn common(l1: &Vec<i32>, l2: &Vec<i32>) -> (c: Set<i32>)
    ensures 
        (forall|i: i32| c.contains(i) ==> l1@.contains(i) && l2@.contains(i)) &&
        (forall|i: i32| l1@.contains(i) && l2@.contains(i) ==> c.contains(i))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatches by using nat for loop index and removed assume */
    let mut result = Set::<i32>::empty();
    let mut i: nat = 0;
    while i < l1@.len()
        invariant
            i <= l1@.len(),
            (forall |x: i32| result.contains(x) ==> l1@.contains(x) && l2@.contains(x)),
            (forall |x: i32| (exists |j: nat| j < i && l1@[j] == x && l2@.contains(x)) ==> result.contains(x)),
        decreases l1@.len() - i
    {
        let elem = l1@[i];
        if l2@.contains(elem) {
            result = result.insert(elem);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}