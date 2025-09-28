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
    /* code modified by LLM (iteration 5): use exec mode for Set operations */
    let mut result = Set::<i32>::empty();
    let mut i = 0;
    while i < l1.len()
        invariant
            i <= l1.len(),
            forall|x: i32| result.contains(x) ==> l1@.contains(x) && l2@.contains(x),
            forall|j: int| 0 <= j < i ==> (l2@.contains(l1@[j]) ==> result.contains(l1@[j]))
    {
        let elem = l1[i];
        let mut j = 0;
        let mut found = false;
        while j < l2.len()
            invariant
                j <= l2.len(),
                found ==> l2@.contains(elem),
                !found ==> forall|k: int| 0 <= k < j ==> l2@[k] != elem
        {
            if l2[j] == elem {
                found = true;
                break;
            }
            j += 1;
        }
        if found {
            result = result.insert(elem);
        }
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}