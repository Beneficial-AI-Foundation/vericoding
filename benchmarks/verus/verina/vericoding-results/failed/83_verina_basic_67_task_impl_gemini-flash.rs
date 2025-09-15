// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helper needed for this problem. */
// </vc-helpers>

// <vc-spec>
fn is_palindrome(x: Seq<char>) -> (result: bool)
    ensures
        result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - 1 - i]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed `i` to `int` and explicitly cast `x.len()` to `int` in the `invariant` for `j`. */
{
    if x.len() == 0 || x.len() == 1 {
        return true;
    }

    let mut i: int = 0;
    while i < (x.len() / 2) as int
        invariant
            0 <= i,
            i <= (x.len() / 2) as int,
            // For elements already checked, they must match their symmetric counterparts
            forall|j: int| 0 <= j < i ==> #[trigger] x[j as nat] == x[ (x.len() as int - 1 - j) as nat ],
        decreases (x.len() / 2) as int - i
    {
        // Check if the current pair of characters matches
        if x[i as nat] != x[ (x.len() as int - 1 - i) as nat ] {
            return false;
        }
        i = i + 1;
    }
    return true;
}
// </vc-code>

}
fn main() {}