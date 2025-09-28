// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int) -> bool {
  a >= 1 && b > a && b < 499500
}

spec fn valid_snow_depth(a: int, b: int, depth: int) -> bool {
  depth >= 1 &&
  ((b - a) * (b - a) - (a + b)) >= 2 &&
  ((b - a) * (b - a) - (a + b)) % 2 == 0
}

spec fn snow_depth_formula(a: int, b: int) -> int
  recommends valid_input(a, b) && valid_snow_depth(a, b, ((b - a) * (b - a) - (a + b)) / 2)
{
  ((b - a) * (b - a) - (a + b)) / 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemmas to help prove preconditions */
fn checked_add(a: i8, b: i8) -> (result: i8)
    requires a as int + b as int >= -128 && a as int + b as int <= 127
    ensures result as int == a as int + b as int
{
    a + b
}

fn checked_sub(a: i8, b: i8) -> (result: i8)
    requires a as int - b as int >= -128 && a as int - b as int <= 127
    ensures result as int == a as int - b as int
{
    a - b
}

fn checked_mul(a: i8, b: i8) -> (result: i8)
    requires a as int * b as int >= -128 && a as int * b as int <= 127
    ensures result as int == a as int * b as int
{
    a * b
}

fn checked_div(a: i8, b: i8) -> (result: i8)
    requires
        b != 0,
        a as int % b as int == 0,
        a as int / b as int >= -128,
        a as int / b as int <= 127,
    ensures result as int == a as int / b as int
{
    a / b
}

proof fn lemma_bounds_for_sum(a: i8, b: i8)
    requires
        a >= 1,
        b > a,
        b < 100,
    ensures a as int + b as int >= -128 && a as int + b as int <= 127
{
}

proof fn lemma_bounds_for_diff_squared(a: i8, b: i8)
    requires
        a >= 1,
        b > a,
        b < 100,
    ensures (b as int - a as int) * (b as int - a as int) >= -128 && (b as int - a as int) * (b as int - a as int) <= 127
{
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
  requires valid_input(a as int, b as int) && valid_snow_depth(a as int, b as int, ((b as int - a as int) * (b as int - a as int) - (a as int + b as int)) / 2)
  ensures result as int >= 1 && result as int == snow_depth_formula(a as int, b as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): direct computation with proof blocks */
    let diff = b as int - a as int;
    let sum = a as int + b as int;
    let diff_squared = diff * diff;
    let numerator = diff_squared - sum;
    let depth = numerator / 2;
    
    proof {
        assert(diff >= 1);
        assert(diff_squared >= 1);
        assert(numerator >= 1);
        assert(depth >= 1);
        assert(depth == snow_depth_formula(a as int, b as int));
    }
    
    depth as i8
}
// </vc-code>


}

fn main() {}