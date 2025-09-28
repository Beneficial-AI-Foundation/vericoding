// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn cubes_for_level(level: int) -> int
    recommends level >= 1
{
    level * (level + 1) / 2
}

spec fn total_cubes_for_height(h: int) -> int
    recommends h >= 1
{
    h * (h + 1) * (h + 2) / 6
}

spec fn valid_pyramid_height(n: int, h: int) -> bool {
    valid_input(n) && h >= 1 && 
    total_cubes_for_height(h) <= n &&
    total_cubes_for_height(h + 1) > n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed 'lemma' keyword from declaration */
fn lemma_total_cubes_increasing_for_h(h: int)
    requires h >= 1
    ensures total_cubes_for_height(h + 1) > total_cubes_for_height(h)
{
    assert((h + 1) * (h + 2) * (h + 3) / 6 > h * (h + 1) * (h + 2) / 6) by {
        assert forall |h_idx: int| h_idx >= 1 implies (h_idx + 1) * (h_idx + 2) * (h_idx + 3) / 6 > h_idx * (h_idx + 1) * (h_idx + 2) / 6 by {
            if h_idx >= 1 {
                let term1 = h_idx * (h_idx + 1) * (h_idx + 2);
                let term2 = (h_idx + 1) * (h_idx + 2) * (h_idx + 3);
                assert(term2 - term1 == 3 * (h_idx + 1) * (h_idx + 2));
                assert(3 * (h_idx + 1) * (h_idx + 2) > 0) by { assert(h_idx + 1 >= 2); assert(h_idx + 2 >= 3); }
                assert(term2 > term1);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures 
        result >= 1 &&
        valid_pyramid_height(n as int, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): constraint h to i8 max */
{
    let n_int = n as int;
    let mut h: int = 1;

    while h < 20 && total_cubes_for_height(h + 1) <= n_int
        invariant
            h >= 1,
            total_cubes_for_height(h) <= n_int,
            n_int >= 1,
            h < 20 // Based on i8 max (127)
        decreases ((127 as int) + 1 - h)
    {
        proof {
            lemma_total_cubes_increasing_for_h(h);
        }
        h = h + 1;
    }
    
    (h as i8)
}
// </vc-code>


}

fn main() {}