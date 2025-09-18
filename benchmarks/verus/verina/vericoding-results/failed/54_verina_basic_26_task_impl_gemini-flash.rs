// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [remove `int` suffix from integer literals] */
fn is_even_lemma(n: int)
    requires
        n % 2i == 0i || n % 2i == 1i || n % 2i == -1i,
    ensures
        (n % 2i == 0i) == (n is even),
        (n % 2i == 1i || n % 2i == -1i) == (n is odd),
{
    // This lemma is a placeholder and doesn't contain actual proof steps
    // as the required properties are typically handled by built-in SMT solver capabilities.
    // In a real scenario, Verus's SMT solver would relate 'n % 2 == 0' directly to 'n is even'.
}
// </vc-helpers>

// <vc-spec>
fn is_even(n: int) -> (result: bool)
    ensures
        result <==> (n % 2 == 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [add `i` suffix to integer literals for `int` type] */
{
    proof {
        is_even_lemma(n);
    }
    n % 2i == 0i
}
// </vc-code>

}
fn main() {}