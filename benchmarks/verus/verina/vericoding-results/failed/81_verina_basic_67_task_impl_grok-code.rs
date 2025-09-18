// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_palindrome(x: Seq<char>) -> (result: bool)
    ensures
        result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - 1 - i]),
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): Fixed type mismatches by using int for indices and added len variable */
    let len = x.len() as int;
    let mut i: int = 0;
    while i < len / 2
        invariant
            forall|j: int| 0 <= j < i ==> #[trigger] x[j] == x[len - 1 - j]
    {
        if x[i] != x[len - 1 - i] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}