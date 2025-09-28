// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

spec fn valid_input(a: int, b: int, x: int, y: int, z: int) -> bool {
    a >= 0 && b >= 0 && x >= 0 && y >= 0 && z >= 0
}

spec fn yellow_crystals_needed(x: int, y: int) -> int {
    x * 2 + y
}

spec fn blue_crystals_needed(y: int, z: int) -> int {
    y + z * 3
}

spec fn min_additional_crystals(a: int, b: int, x: int, y: int, z: int) -> int {
    max(0, yellow_crystals_needed(x, y) - a) + max(0, blue_crystals_needed(y, z) - b)
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_subtract_inequality()
    ensures 
        forall|x: int, y: int| x >= y ==> x - y >= 0
{
    assert forall|x: int, y: int| x >= y implies x - y >= 0 by {
        // Trivial arithmetic property
    };
}

proof fn lemma_max_0_properties() 
    ensures 
        forall|a: int, b: int| #[trigger] max(0, a + b) <= max(0, a) + max(0, b),
        forall|n: int| #[trigger] max(0, n) >= 0
{
    assert forall|a: int, b: int| #[trigger] max(0, a + b) <= max(0, a) + max(0, b) by {
        if a + b <= 0 {
            assert(max(0, a + b) == 0);
            assert(max(0, a) >= 0);
            assert(max(0, b) >= 0);
        } else {
            assert(max(0, a + b) == a + b);
            assert(max(0, a) >= a);
            assert(max(0, b) >= b);
        }
    };
    
    assert forall|n: int| #[trigger] max(0, n) >= 0 by {
        if n <= 0 {
            assert(max(0, n) == 0);
        } else {
            assert(max(0, n) == n);
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, x: i8, y: i8, z: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int, x as int, y as int, z as int)
    ensures 
        result >= 0,
        result as int == min_additional_crystals(a as int, b as int, x as int, y as int, z as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): remove call to missing lemma and simplify proof */
    let yellow_needed = x * 2 + y;
    let blue_needed = y + z * 3;
    
    let yellow_shortage = if yellow_needed > a { yellow_needed - a } else { 0 };
    let blue_shortage = if blue_needed > b { blue_needed - b } else { 0 };
    
    proof {
        lemma_max_0_properties();
        
        assert(yellow_shortage as int == max(0, yellow_needed as int - a as int));
        assert(blue_shortage as int == max(0, blue_needed as int - b as int));
        assert((yellow_shortage + blue_shortage) as int == min_additional_crystals(a as int, b as int, x as int, y as int, z as int));
    }
    
    let total = yellow_shortage + blue_shortage;
    
    assert(total >= 0) by {
        assert(yellow_shortage >= 0 && blue_shortage >= 0);
    };
    
    total
}
// </vc-code>


}

fn main() {}