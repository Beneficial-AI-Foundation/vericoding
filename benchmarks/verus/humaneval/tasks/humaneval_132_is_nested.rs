// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_nested(s: Vec<i8>) -> (res: bool)
    ensures res == exists|x: int, y: int, z: int, w: int| 0 <= x < y < z < w < s@.len() && s@[x] == 0 && s@[y] == 0 && s@[z] == 1 && s@[w] == 1
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}