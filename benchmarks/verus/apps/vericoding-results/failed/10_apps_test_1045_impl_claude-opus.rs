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
/* helper modified by LLM (iteration 5): Fixed lemma proofs with correct arithmetic reasoning */
proof fn lemma_cubes_for_level_positive(level: int)
    requires level >= 1
    ensures cubes_for_level(level) >= 1
{
    assert(level >= 1);
    assert(level + 1 >= 2);
    assert(level * (level + 1) >= 1 * 2) by {
        assert(level >= 1);
        assert(level + 1 >= 2);
    }
    assert(level * (level + 1) >= 2);
    assert(level * (level + 1) / 2 >= 1);
}

proof fn lemma_total_cubes_monotonic(h: int)
    requires h >= 1
    ensures total_cubes_for_height(h) < total_cubes_for_height(h + 1)
{
    assert(total_cubes_for_height(h) == h * (h + 1) * (h + 2) / 6);
    assert(total_cubes_for_height(h + 1) == (h + 1) * (h + 2) * (h + 3) / 6);
    
    let lhs = h * (h + 1) * (h + 2);
    let rhs = (h + 1) * (h + 2) * (h + 3);
    
    assert((h + 1) * (h + 2) > 0) by {
        assert(h >= 1);
        assert(h + 1 >= 2);
        assert(h + 2 >= 3);
    }
    assert(h + 3 > h);
    assert(rhs == (h + 1) * (h + 2) * (h + 3));
    assert(lhs == h * (h + 1) * (h + 2)) by {
        assert(h >= 1);
    }
    assert(rhs > lhs) by {
        assert((h + 1) * (h + 2) > 0);
        assert(h + 3 > h);
    }
    assert(rhs / 6 > lhs / 6);
}

proof fn lemma_total_cubes_bounds(h: int)
    requires h >= 1
    ensures total_cubes_for_height(h) >= h
{
    assert(h >= 1);
    assert(h + 1 >= 2);
    assert(h + 2 >= 3);
    assert((h + 1) * (h + 2) >= 2 * 3) by {
        assert(h + 1 >= 2);
        assert(h + 2 >= 3);
    }
    assert((h + 1) * (h + 2) >= 6);
    assert(h * (h + 1) * (h + 2) >= h * 6) by {
        assert((h + 1) * (h + 2) >= 6);
        assert(h >= 1);
    }
    assert(h * (h + 1) * (h + 2) / 6 >= h);
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
    /* code modified by LLM (iteration 5): Use exec-mode variables and ghost tracking for verification */
    let mut h: i8 = 1;
    let mut total: i8 = 1;
    
    proof {
        assert(total == total_cubes_for_height(1));
    }
    
    while h < 20 && total <= n
        invariant
            h >= 1,
            h <= 20,
            total == total_cubes_for_height(h as int),
            total <= n,
            total_cubes_for_height(h as int) <= 127,
        decreases 20 - h
    {
        let ghost h_int = h as int;
        let ghost next_h = h_int + 1;
        
        proof {
            assert(next_h == h_int + 1);
            assert(cubes_for_level(next_h) == next_h * (next_h + 1) / 2);
            assert(total_cubes_for_height(next_h) == total_cubes_for_height(h_int) + cubes_for_level(next_h));
            lemma_total_cubes_monotonic(h_int);
        }
        
        let next_level: i8 = ((h + 1) * (h + 2) / 2) as i8;
        proof {
            assert(next_level as int == (h + 1) as int * (h + 2) as int / 2);
            assert(next_level as int <= 127) by {
                assert(h < 20);
                assert(h + 1 <= 20);
                assert(h + 2 <= 21);
                assert((h + 1) as int * (h + 2) as int <= 20 * 21);
                assert(20 * 21 / 2 == 210);
                assert(next_level as int <= 210);
            }
        }
        
        let new_total = total + next_level;
        
        proof {
            assert(new_total as int <= 127) by {
                assert(h < 20);
                assert(total_cubes_for_height(next_h) <= 127);
                assert(new_total as int == total_cubes_for_height(next_h));
            }
        }
        
        if new_total > n {
            proof {
                assert(total == total_cubes_for_height(h as int));
                assert(total <= n);
                assert(total_cubes_for_height((h + 1) as int) == new_total as int);
                assert(total_cubes_for_height((h + 1) as int) > n as int);
                assert(valid_pyramid_height(n as int, h as int));
            }
            return h;
        }
        
        h = h + 1;
        total = new_total;
    }
    
    proof {
        assert(total_cubes_for_height(h as int) == total as int);
        assert(total <= n);
        
        if h < 20 {
            assert(total == n);
            lemma_total_cubes_monotonic(h as int);
            assert(total_cubes_for_height((h + 1) as int) > n as int);
        }
        
        assert(valid_pyramid_height(n as int, h as int));
    }
    
    h
}
// </vc-code>


}

fn main() {}