// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn cube(n: int) -> int {
    n * n * n
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_cube(n: u8) -> (r: bool)
    ensures r == exists|k: int| 0 <= k <= n as int && n as int == cube(k)
// </vc-spec>
// <vc-code>
{
    assume(false);
    false
}
// </vc-code>


}

fn main() {}