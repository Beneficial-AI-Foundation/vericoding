// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn is_even_proof(n: int) -> (result: bool)
    ensures
        result <==> (n % 2 == 0),
{
    /* helper modified by LLM (iteration 5): use native integer operations without ghost types */
    if n % 2 == 0 {
        true
    } else {
        false
    }
}
// </vc-helpers>

// <vc-spec>
fn is_even(n: int) -> (result: bool)
    ensures
        result <==> (n % 2 == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use native integer operations without ghost types */
    n % 2 == 0
}
// </vc-code>

}
fn main() {}