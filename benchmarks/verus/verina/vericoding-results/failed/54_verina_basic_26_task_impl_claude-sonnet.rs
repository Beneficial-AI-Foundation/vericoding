// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_even(n: int) -> (result: bool)
    ensures
        result <==> (n % 2 == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use correct int literal syntax */
    (n % 2) == 0int
}
// </vc-code>

}
fn main() {}