// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_palindrome_symmetric(x: Seq<char>, i: int)
    requires
        0 <= i < x.len(),
        forall|j: int| 0 <= j < x.len() ==> #[trigger] x[j] == x[x.len() - 1 - j],
    ensures
        x[i] == x[x.len() - 1 - i]
{
    assert(x[i] == x[x.len() - 1 - i]);
}
/* helper modified by LLM (iteration 5): Fixed type conversion in executable code */
// </vc-helpers>

// <vc-spec>
fn is_palindrome(x: Seq<char>) -> (result: bool)
    ensures
        result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - 1 - i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type conversion issues by using usize for indexing */
    let mut left: usize = 0;
    let mut right: usize = (x.len() as usize) - 1;
    while left <= right
        invariant
            left <= right + 1,
            0 <= left <= x.len(),
            0 <= right < x.len(),
            forall|j: int| 0 <= j < left ==> #[trigger] x[j] == x[x.len() - 1 - j],
        decreases right - left
    {
        if x.index(left as int) != x.index(right as int) {
            return false;
        }
        left = left + 1;
        if right > 0 {
            right = right - 1;
        } else {
            break;
        }
    }
    true
}
// </vc-code>

}
fn main() {}