// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int) -> bool {
  a >= 1 && a <= 1000 && b >= 2 && b <= 1000
}

spec fn total_burning_hours(a: int, b: int) -> int
  decreases a via a_decreases
{
  if a <= 0 { 0 }
  else if a < b { a }
  else { a + total_burning_hours(a / b, b) }
}

#[verifier::decreases_by]
proof fn a_decreases(a: int, b: int) {
  assume(false);
}
// </vc-preamble>

// <vc-helpers>
proof fn a_decreases(a: int, b: int) 
    requires
        b > 1,
        a >= 0
    decreases a
    ensures 
        a / b < a
{
    if a > 0 {
        assert(a / b < a) by {
            assert(a <= (a / b) * b + (b - 1));
            /* helper modified by LLM (iteration 5): fixed proof calculation */
            calc! {
                a / b;
                <= (a - 1) / b;
                <= (a - 1) / 2;
                < a;
            }
        };
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
  requires 
    valid_input(a as int, b as int)
  ensures 
    result as int >= a as int,
    result as int == total_burning_hours(a as int, b as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed ensures spec formatting */
    let mut total: i8 = a;
    let mut remaining: i8 = a;
    
    while remaining >= b
        invariant
            remaining >= 0,
            remaining <= a,
            total as int == total_burning_hours((a - remaining) as int, b as int) + remaining as int,
            total as int >= a as int
        decreases remaining
    {
        let burned = remaining / b;
        total = (total + burned) as i8;
        remaining = burned + (remaining % b);
    }
    
    total
}
// </vc-code>


}

fn main() {}