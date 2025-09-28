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
#[verifier::spinoff_prover]
proof fn lemma_total_cubes_recursive(h: int)
    requires
        h >= 1,
    ensures
        total_cubes_for_height(h) == total_cubes_for_height(h - 1) + cubes_for_level(h),
{
}

#[verifier::spinoff_prover]
proof fn lemma_cubes_for_level_recursive(level: int)
    requires
        level >= 1,
    ensures
        cubes_for_level(level + 1) == cubes_for_level(level) + level + 1,
{
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
    let mut h: i8 = 0;
    let mut total_cubes: i8 = 0;
    let mut cubes_for_next_level: i8 = 1;

    while total_cubes <= n - cubes_for_next_level
        invariant
            h >= 0,
            valid_input(n as int),
            total_cubes as int == total_cubes_for_height(h as int),
            cubes_for_next_level as int == cubes_for_level((h + 1) as int),
            total_cubes as int <= n as int,
        decreases (n as int) - (total_cubes as int)
    {
        let h_old = h;
        total_cubes = total_cubes + cubes_for_next_level;
        h = h + 1;
        cubes_for_next_level = cubes_for_next_level + h + 1;

        proof {
            lemma_total_cubes_recursive(h as int);
            lemma_cubes_for_level_recursive(h_old as int + 1);
        }
    }

    proof {
        let h_int = h as int;
        if h_int == 0 {
            assert(1 > n as int) by(nonlinear_arith) requires valid_input(n as int);
            assert(false);
        }
        assert(h_int >= 1);
        
        assert(total_cubes_for_height(h_int) <= n as int);
        lemma_total_cubes_recursive(h_int + 1);
        assert(total_cubes_for_height(h_int + 1) > n as int);
        assert(valid_pyramid_height(n as int, h_int));
    }
    
    h
}
// </vc-code>


}

fn main() {}