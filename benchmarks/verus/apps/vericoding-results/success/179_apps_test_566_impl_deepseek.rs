// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(r: int, g: int, b: int) -> bool {
    r >= 0 && g >= 0 && b >= 0
}

spec fn max_tables(r: int, g: int, b: int) -> int
    recommends valid_input(r, g, b)
{
    min(min(min((r + g + b) / 3, r + g), r + b), g + b)
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}
// </vc-preamble>

// <vc-helpers>

spec fn max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

proof fn lemma_min_min_association(a: int, b: int, c: int)
    ensures
        min(min(a, b), c) == min(a, min(b, c)),
{
}

proof fn lemma_min_sum_property(r: int, g: int, b: int)
    requires
        r >= 0,
        g >= 0,
        b >= 0,
    ensures
        min(min(min((r + g + b) / 3, r + g), r + b), g + b) == min((r + g + b) / 3, min(r + g, min(r + b, g + b))),
{
    lemma_min_min_association(min((r + g + b) / 3, r + g), r + b, g + b);
    lemma_min_min_association(r + g, r + b, g + b);
}

// </vc-helpers>

// <vc-spec>
fn solve(r: i8, g: i8, b: i8) -> (result: i8)
    requires 
        valid_input(r as int, g as int, b as int)
    ensures 
        result as int == max_tables(r as int, g as int, b as int),
        result >= 0
// </vc-spec>
// <vc-code>
{
    let red = r as i16;
    let green = g as i16;
    let blue = b as i16;
    
    let sum = red + green + blue;
    let rg_sum = red + green;
    let rb_sum = red + blue;
    let gb_sum = green + blue;
    
    let candidate1 = sum / 3;
    let candidate2 = rg_sum;
    let candidate3 = rb_sum;
    let candidate4 = gb_sum;
    
    let mut result = candidate1;
    
    if candidate2 < result {
        result = candidate2;
    }
    
    if candidate3 < result {
        result = candidate3;
    }
    
    if candidate4 < result {
        result = candidate4;
    }
    
    (result as i8)
}
// </vc-code>


}

fn main() {}