// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn cube(n: nat) -> nat { n * n * n }
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): remove inner proof block; provide constant cube equalities for 0..7 */
proof fn cube_constants()
    ensures
        cube(0) == 0,
        cube(1) == 1,
        cube(2) == 8,
        cube(3) == 27,
        cube(4) == 64,
        cube(5) == 125,
        cube(6) == 216,
        cube(7) == 343,
{
    assert(cube(0) == 0);
    assert(cube(1) == 1);
    assert(cube(2) == 8);
    assert(cube(3) == 27);
    assert(cube(4) == 64);
    assert(cube(5) == 125);
    assert(cube(6) == 216);
    assert(cube(7) == 343);
}
// </vc-helpers>

// <vc-spec>
fn cube_root(n: u8) -> (r: u8)
    ensures 
        cube(r as nat) <= n as nat,
        (n as nat) < cube((r as nat) + 1),
        r as nat <= n as nat,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): piecewise selection with cube constant lemma; removed invalid spec-proof block */
    proof { cube_constants(); }
    if n < 1u8 {
        proof {
            assert(cube(0) == 0);
            assert(cube(0) <= n as nat);
            assert((n as nat) < cube(0 + 1));
            assert((0 as nat) <= n as nat);
        }
        0u8
    } else if n < 8u8 {
        proof {
            assert(cube(1) == 1);
            assert(cube(1) <= n as nat);
            assert((n as nat) < cube(1 + 1));
            assert((1 as nat) <= n as nat);
        }
        1u8
    } else if n < 27u8 {
        proof {
            assert(cube(2) == 8);
            assert(cube(2) <= n as nat);
            assert((n as nat) < cube(2 + 1));
            assert((2 as nat) <= n as nat);
        }
        2u8
    } else if n < 64u8 {
        proof {
            assert(cube(3) == 27);
            assert(cube(3) <= n as nat);
            assert((n as nat) < cube(3 + 1));
            assert((3 as nat) <= n as nat);
        }
        3u8
    } else if n < 125u8 {
        proof {
            assert(cube(4) == 64);
            assert(cube(4) <= n as nat);
            assert((n as nat) < cube(4 + 1));
            assert((4 as nat) <= n as nat);
        }
        4u8
    } else if n < 216u8 {
        proof {
            assert(cube(5) == 125);
            assert(cube(5) <= n as nat);
            assert((n as nat) < cube(5 + 1));
            assert((5 as nat) <= n as nat);
        }
        5u8
    } else {
        proof {
            assert(cube(6) == 216);
            assert(cube(6) <= n as nat);
            assert((n as nat) < cube(6 + 1));
            assert((6 as nat) <= n as nat);
        }
        6u8
    }
}
// </vc-code>


}

fn main() {}