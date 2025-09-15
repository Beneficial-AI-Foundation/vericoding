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
    /* code modified by LLM (iteration 5): Fixed ghost/exec type usage by using usize for loop bounds */
    let len = x.len();
    let mut i: usize = 0;
    while i < len / 2
        invariant
            i <= len / 2,
            forall|j: int| 0 <= j < i ==> x[j] == x[len - 1 - j]
    {
        if x[i as int] != x[len - 1 - (i as int)] {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}