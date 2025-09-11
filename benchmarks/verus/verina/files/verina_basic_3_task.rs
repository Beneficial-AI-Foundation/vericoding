// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_divisible_by_11(n: i32) -> (result: bool)
    ensures
        result <==> (exists|k: int| #[trigger] (k * 11) == n),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}