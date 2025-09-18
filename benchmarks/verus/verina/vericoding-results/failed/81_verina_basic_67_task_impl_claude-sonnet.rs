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
    /* code modified by LLM (iteration 3): use sequence indexing with @ operator */
    let n = x.len();
    let mut i: usize = 0;
    while i < n / 2
        invariant
            0 <= i <= n / 2,
            forall|j: int| 0 <= j < i ==> x[j] == x[n - 1 - j],
    {
        if x[i as int] != x[n - 1 - i as int] {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}