// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove that inserting x yields set containing x */
proof fn insert_contains(s: Set<i32>, x: i32)
    ensures
        s.insert(x).contains(x),
{
    proof {
        assert(s.insert(x).contains(x));
    }
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
    /* code modified by LLM (iteration 5): iterate over l1 with nat index and build intersection set */
    let mut s: Set<i32> = Set::empty();
    let mut i: nat = 0;
    while i < l1@.len()
        invariant
            i <= l1@.len(),
            (forall|x: i32| s.contains(x) ==> (exists|j: nat| j < i && l1@[j] == x) && l2@.contains(x)),
            (forall|x: i32| (exists|j: nat| j < i && l1@[j] == x) && l2@.contains(x) ==> s.contains(x)),
        decreases l1@.len() - i
    {
        let v = l1@[i];
        if l2@.contains(v) {
            s = s.insert(v);
        }
        i = i + 1;
    }
    s
}

// </vc-code>


}

fn main() {}