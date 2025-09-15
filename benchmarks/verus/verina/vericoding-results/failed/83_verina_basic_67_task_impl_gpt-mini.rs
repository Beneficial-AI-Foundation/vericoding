// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): min helper */
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn is_palindrome(x: Seq<char>) -> (result: bool)
    ensures
        result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - 1 - i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): check palindrome by iterating over all indices with invariant */
    let n: int = x.len();
    let mut i: int = 0;
    let mut ok: bool = true;
    while i < n
        invariant 0 <= i && i <= n
        invariant ok == (forall |j: int| 0 <= j < i ==> x@[j] == x@[n - 1 - j])
        decreases n - i
    {
        let pair_eq: bool = x@[i] == x@[n - 1 - i];
        ok = ok && pair_eq;
        i = i + 1;
    }
    ok
}
// </vc-code>

}
fn main() {}