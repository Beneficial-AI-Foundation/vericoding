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

/* helper modified by LLM (iteration 5): fixed a_decreases proof to ensure measure decreases with proper assertions without assumptions */
#[verifier::decreases_by]
proof fn a_decreases(a: int, b: int)
  requires b >= 2
{
  if a <= 0 {
  } else if a < b {
    assert(a / b == 0);
  } else {
    assert(b >= 2);
    assert(a / b < a);
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
    /* code modified by LLM (iteration 5): implemented iterative calculation using int to avoid overflow, with correct invariant */
    let mut remaining: int = a as int;
    let mut total: int = 0;
    while remaining >= b as int
      invariant
        total + total_burning_hours(remaining, b as int) == total_burning_hours(a as int, b as int),
        remaining >= 0,
        total >= 0,
      decreases remaining
    {
      total = total + remaining;
      remaining = remaining / (b as int);
    }
    (total + remaining) as i8
}
// </vc-code>


}

fn main() {}