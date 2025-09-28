// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(h: int, a: int) -> bool {
    h >= 1 && a >= 1
}

spec fn is_minimum_attacks(attacks: int, h: int, a: int) -> bool {
    attacks >= 1 &&
    attacks * a >= h &&
    (attacks - 1) * a < h
}

spec fn ceil_div(h: int, a: int) -> int
    recommends a > 0
{
    (h + a - 1) / a
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma declaration syntax by removing 'lemma' keyword and using 'fn' with proof attribute */
proof fn lemma_ceil_div_properties(h: int, a: int)
    requires
        h >= 1,
        a >= 1,
    ensures
        ceil_div(h, a) >= 1,
        ceil_div(h, a) * a >= h,
        (ceil_div(h, a) - 1) * a < h,
{
    let result = ceil_div(h, a);
    assert(result == (h + a - 1) / a);
    
    // Prove result >= 1
    assert(h + a - 1 >= a) by {
        assert(h >= 1);
    }
    assert(result >= 1);
    
    // Prove result * a >= h
    assert(result * a >= h) by {
        let numerator = h + a - 1;
        assert(numerator / a * a <= numerator);
        assert(result * a >= h + a - 1 - (a - 1));
        assert(result * a >= h);
    }
    
    // Prove (result - 1) * a < h
    assert((result - 1) * a < h) by {
        let numerator = h + a - 1;
        assert(numerator / a * a > numerator - a);
        assert(result * a > h + a - 1 - a);
        assert(result * a > h - 1);
        assert((result - 1) * a < h);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(h: i8, a: i8) -> (attacks: i8)
    requires 
        valid_input(h as int, a as int)
    ensures 
        is_minimum_attacks(attacks as int, h as int, a as int),
        attacks as int == ceil_div(h as int, a as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute result directly using exec operations */
    let result = ((h as i8) + (a as i8) - 1) / (a as i8);
    
    proof {
        lemma_ceil_div_properties(h as int, a as int);
        assert(result as int == ceil_div(h as int, a as int));
    }
    
    result
}
// </vc-code>


}

fn main() {}