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
/* helper modified by LLM (iteration 5): remove ensures clause with exec function call and move to body */
exec fn compute_total_burning_hours(a: i32, b: i32) -> (result: i32)
  requires
    valid_input(a as int, b as int)
  decreases a
{
  if a <= 0 {
    0
  } else if a < b {
    a
  } else {
    a + compute_total_burning_hours(a / b, b)
  }
}

/* helper modified by LLM (iteration 5): change lemma to call exec function in body and remove ensures clause */
proof fn lemma_compute_equals_spec(a: int, b: int)
  requires
    valid_input(a, b)
{
  let res = compute_total_burning_hours(a as i32, b as i32);
  assert(res as int == total_burning_hours(a, b));
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
  /* code modified by LLM (iteration 5): update to call modified lemma without ensures clause */
  let a_i32 = a as i32;
  let b_i32 = b as i32;
  let total_i32 = compute_total_burning_hours(a_i32, b_i32);
  proof {
    lemma_compute_equals_spec(a_i32 as int, b_i32 as int);
  }
  let result = total_i32 as i8;
  result
}
// </vc-code>


}

fn main() {}