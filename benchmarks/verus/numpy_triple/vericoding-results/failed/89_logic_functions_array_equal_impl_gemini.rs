// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_equal<T>(a1: &Vec<T>, a2: &Vec<T>) -> (result: bool)
    where T: PartialEq<T>,
    requires a1.len() == a2.len(),
    ensures 
        result == true <==> (forall|i: int| 0 <= i < a1.len() as int ==> a1@[i] == a2@[i]) &&
        (a1.len() == 0 ==> result == true) &&
        (exists|i: int| 0 <= i < a1.len() as int && !(a1@[i] == a2@[i]) ==> result == false)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): expanded proof blocks and added assertions for postconditions */
    let mut i: usize = 0;
    while i < a1.len()
        invariant
            a1.len() == a2.len(),
            0 <= i <= a1.len(),
            forall|j: int| 0 <= j < i as int ==> a1@[j] == a2@[j],
        decreases a1.len() - i
    {
        if a1[i] != a2[i] {
            assert(!(a1@[i as int] == a2@[i as int]));
            assert(exists|k: int| 0 <= k < a1.len() as int && !(a1@[k] == a2@[k]));
            return false;
        }

        assert forall|j: int| 0 <= j < (i + 1) as int implies a1@[j] == a2@[j] by {
            if j < i as int {
                // This case is covered by the loop invariant.
            } else {
                // This case must be j == i.
                assert(j == i as int);
                // And for j==i, equality holds because the `if` condition was false.
                assert(a1@[i as int] == a2@[i as int]);
            }
        }

        i = i + 1;
    }
    
    assert(forall|j: int| 0 <= j < a1.len() as int ==> a1@[j] == a2@[j]);
    return true;
}
// </vc-code>

}
fn main() {}