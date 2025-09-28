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
/* helper modified by LLM (iteration 5): fixed precondition check and termination issues */
proof fn total_burning_hours_monotonic(a: int, b: int)
    requires
        a >= 1,
        b >= 2
    ensures
        total_burning_hours(a, b) >= a
    decreases a
{
    if a < b {
        assert(total_burning_hours(a, b) == a);
    } else {
        assert(a / b >= 1);
        total_burning_hours_monotonic(a / b, b);
        assert(total_burning_hours(a, b) == a + total_burning_hours(a / b, b));
        assert(total_burning_hours(a / b, b) >= 0);
        assert(total_burning_hours(a, b) >= a);
    }
}

fn solve_recursive(a: i8, b: i8) -> (result: i8)
    requires
        valid_input(a as int, b as int)
    ensures
        result as int == total_burning_hours(a as int, b as int)
    decreases a
{
    if a < b {
        a
    } else {
        let next_a = a / b;
        assert(valid_input(next_a as int, b as int));
        let recursive_result = solve_recursive(next_a, b);
        a + recursive_result
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
    /* code modified by LLM (iteration 5): added assertion for precondition */
    proof {
        assert(a >= 1);
        total_burning_hours_monotonic(a as int, b as int);
    }
    let result = solve_recursive(a, b);
    result
}
// </vc-code>


}

fn main() {}