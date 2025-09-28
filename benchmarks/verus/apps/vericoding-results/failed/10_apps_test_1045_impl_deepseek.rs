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
proof fn lemma_total_cubes_monotonic(h: int)
    requires h >= 1
    ensures total_cubes_for_height(h) <= total_cubes_for_height(h + 1)
{
    let cubes = cubes_for_level(h + 1);
    assert(total_cubes_for_height(h + 1) == total_cubes_for_height(h) + cubes);
    assert(cubes >= 0);
    /* helper modified by LLM (iteration 5): added missing monotonicity lemma */
}

proof fn lemma_total_cubes_cast(h: int)
    requires h >= 1, h <= i8::MAX as int
    ensures total_cubes_for_height(h) as i32 == total_cubes_for_height(h)
{
    /* helper modified by LLM (iteration 5): kept as-is */
}

proof fn lemma_find_height_bound(n: int, h: int)
    requires 
        valid_input(n),
        h >= 1,
        total_cubes_for_height(h) <= n
    ensures valid_pyramid_height(n, h) || total_cubes_for_height(h + 1) <= n
{
    if total_cubes_for_height(h + 1) <= n {
    } else {
        assert(total_cubes_for_height(h + 1) > n);
        assert(valid_pyramid_height(n, h));
    }
    /* helper modified by LLM (iteration 5): removed call to non-existent lemma */
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
    /* code modified by LLM (iteration 5): replaced lemma_total_cubes_monotonic calls with lemma_total_cubes_monotonic */
    let n_i32 = n as i32;
    let mut h: i8 = 1;
    let mut total: i32 = 0;
    
    assert(total_cubes_for_height(1) == 1);
    assert(1 <= n_i32);
    
    while total <= n_i32 && h < i8::MAX
        invariant
            1 <= h <= i8::MAX,
            total == total_cubes_for_height(h as int) as i32,
            total <= n_i32
        decreases (i8::MAX - h) as int
    {
        assert(h < i8::MAX);
        let next_h = h + 1;
        
        assert(next_h >= 2);
        proof { lemma_total_cubes_monotonic(h as int); }
        
        let level_cubes: i32 = ((h as i32) * (h as i32 + 1)) / 2;
        assert(level_cubes >= 1);
        
        let new_total = total + level_cubes;
        assert(new_total == total_cubes_for_height(next_h as int));
        
        if new_total <= n_i32 {
            total = new_total;
            h = next_h;
        } else {
            break;
        }
    }
    
    proof {
        lemma_find_height_bound(n as int, h as int);
        assert(valid_pyramid_height(n as int, h as int));
    }
    
    h
}
// </vc-code>


}

fn main() {}