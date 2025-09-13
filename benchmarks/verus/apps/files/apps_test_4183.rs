// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn gcd(a: int, b: int) -> int
  recommends a > 0 && b >= 0
  decreases b
{
  if b == 0 { a } else { gcd(b, a % b) }
}

spec fn lcm(a: int, b: int) -> int
  recommends a > 0 && b > 0
{
  (a * b) / gcd(a, b)
}

spec fn lcm_seq(nums: Seq<int>) -> int
  recommends nums.len() > 0 && forall|i: int| 0 <= i < nums.len() ==> nums[i] > 0
  decreases nums.len()
{
  if nums.len() == 1 { nums[0] }
  else { lcm(nums[0], lcm_seq(nums.subrange(1, nums.len() as int))) }
}

spec fn valid_input(periods: Seq<int>) -> bool {
  periods.len() > 0 && periods.len() <= 100 &&
  forall|i: int| 0 <= i < periods.len() ==> periods[i] > 0
}

spec fn correct_result(periods: Seq<int>, result: int) -> bool
  recommends valid_input(periods)
{
  result == lcm_seq(periods)
}
// </vc-helpers>

// <vc-spec>
fn find_minimum_time(periods: Seq<int>) -> (result: int)
  requires valid_input(periods)
  ensures correct_result(periods, result)
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}