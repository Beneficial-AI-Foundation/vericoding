// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for prefix equality */
spec fn prefix_eq<T>(a1: &Vec<T>, a2: &Vec<T>, len: int) -> bool
    where T: PartialEq<T>,
    requires 0 <= len && len <= a1.len() && len <= a2.len()
{
    forall|i: int| 0 <= i && i < len ==> a1@[i] == a2@[i]
}
// </vc-helpers>

// <vc-spec>
fn array_equal<T>(a1: &Vec<T>, a2: &Vec<T>) -> (result: bool)
    where T: PartialEq<T>,
    requires a1.len() == a2.len(),
    ensures 
        result == true <==> (forall|i: int| 0 <= i < a1.len() ==> a1[i] == a2[i]) &&
        (a1.len() == 0 ==> result == true) &&
        (exists|i: int| 0 <= i < a1.len() && !(a1[i] == a2[i]) ==> result == false)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate with invariants using prefix_eq helper and short-circuit on mismatch */
    let mut i: int = 0;
    let mut ok: bool = true;
    while i < a1.len()
        invariant 0 <= i && i <= a1.len()
        invariant ok ==> prefix_eq(a1, a2, i)
        invariant (!ok) ==> (exists|j: int| 0 <= j && j < i && a1@[j] != a2@[j])
        decreases a1.len() - i
    {
        if a1@[i] == a2@[i] {
            i = i + 1;
        } else {
            let idx = i;
            ok = false;
            i = a1.len();
            proof {
                assert(0 <= idx && idx < a1.len());
                assert(a1@[idx] != a2@[idx]);
                assert(exists|j: int| 0 <= j && j < i && a1@[j] != a2@[j]);
            }
        }
    }
    ok
}
// </vc-code>

}
fn main() {}