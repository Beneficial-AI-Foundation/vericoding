// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn tile_rectangle(n: u32, m: u32) -> (result: u32)
    requires 
        n > 0,
        m > 0,
    ensures
        result >= 1,
        result <= n * m,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>

}

fn main() {
    // Apps difficulty: interview
    // Assurance level: guarded

    // info: 3
    // assert(tile_rectangle(2, 3) == 3);

    // info: 5
    // assert(tile_rectangle(5, 8) == 5);

    // info: 6
    // assert(tile_rectangle(11, 13) == 6);
}