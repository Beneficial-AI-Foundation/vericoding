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
/* helper modified by LLM (iteration 5): removed ghost int usage from exec function */
proof fn lemma_total_cubes_monotonic(h: int)
    requires h >= 1
    ensures total_cubes_for_height(h + 1) > total_cubes_for_height(h)
{
}

proof fn lemma_total_cubes_bounds(h: int)
    requires h >= 1
    ensures total_cubes_for_height(h) >= h
{
}

proof fn lemma_search_correctness(n: int, h: int)
    requires
        valid_input(n),
        h >= 1,
        total_cubes_for_height(h) <= n,
        total_cubes_for_height(h + 1) > n
    ensures valid_pyramid_height(n, h)
{
}

fn total_cubes_exec(h: i8) -> (result: i8)
    requires h >= 1
    ensures result == total_cubes_for_height(h as int) as i8
{
    let h_i32 = h as i32;
    ((h_i32 * (h_i32 + 1) * (h_i32 + 2)) / 6) as i8
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
{
    /* code modified by LLM (iteration 5): use exec function without ghost types */
    let mut h: i8 = 1;
    
    while total_cubes_exec(h + 1) <= n
        invariant
            h >= 1,
            total_cubes_for_height(h as int) <= n as int,
            h <= 127
        decreases 127 - h
    {
        h = h + 1;
    }
    
    proof {
        lemma_search_correctness(n as int, h as int);
    }
    
    h
}
// </vc-code>


}

fn main() {}