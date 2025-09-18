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
        result == true <==> (forall|i: int| 0 <= i < a1.len() ==> a1[i] == a2[i]) &&
        (a1.len() == 0 ==> result == true) &&
        (exists|i: int| 0 <= i < a1.len() && !(a1[i] == a2[i]) ==> result == false)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use sequence indexing with @ to fix recommendations and preconditions, and changed i to int for cleaner indexing. */
{
    let n: int = a1.len() as int;
    let mut i: nat = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall |k: int| 0 <= k < i ==> a1@[k] == a2@[k]
        decreases n - i
    {
        if a1@[i] != a2@[i] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}