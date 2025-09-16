// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): provide mirror computation as spec function for index symmetry */
spec fn mirror(i: int, len: int) -> int { len - 1 - i }
// </vc-helpers>

// <vc-spec>
fn is_palindrome(text: &str) -> (result: bool)

    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute palindrome via quantified expression using Seq::index and int length */
    let n = text@.len() as int;
    let result = forall|i: int| 0 <= i && i < n ==> #[trigger] text@.index(i) == text@.index(mirror(i, n));
    result
}
// </vc-code>

}
fn main() {}