// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_equiv(a1: Vec<f32>, a2: Vec<f32>) -> (result: bool)
    requires a1.len() == a2.len(),
    ensures result == (forall|i: int| 0 <= i < a1@.len() ==> a1@[i] == a2@[i])
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): Removed unnecessary assert statement causing compilation error to fix expected `,` syntax issue */
    let mut i: usize = 0;
    let mut all_equal: bool = true;
    while i < a1.len()
        invariant
            0 <= i as int <= a1.len() as int,
            a1@.len() == a2@.len(),
            all_equal == (forall|j: int| 0 <= j < i as int ==> a1@[j] == a2@[j])
        decreases (a1.len() - i as int) as int
    {
        if a1@[i as int] != a2@[i as int] {
            all_equal = false;
            proof {
                assert(a1@[i as int] != a2@[i as int]);
                assert(forall|j: int| 0 <= j < i as int ==> a1@[j] == a2@[j])
                    by { for all j | 0 <= j <= (i as int - 1) { assert(a1@[j] == a2@[j]); } };
                assert(!(forall|j: int| 0 <= j < (i as int + 1) ==> a1@[j] == a2@[j]));
            }
        }
        i += 1;
    }
    all_equal
}
// </vc-code>

}
fn main() {}