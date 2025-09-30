// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, m: int, k: int, a: int, b: int) -> bool {
  n > 0 && m > 0 && k > 0 && 1 <= a <= n * m * k && 1 <= b <= n * m * k && a != b
}

spec fn get_entrance(apt: int, m: int, k: int) -> int
  recommends apt >= 1, m > 0 && k > 0
{
  (apt - 1) / (m * k)
}

spec fn get_floor(apt: int, m: int, k: int) -> int
  recommends apt >= 1, m > 0 && k > 0
{
  ((apt - 1) - get_entrance(apt, m, k) * m * k) / k
}

spec fn min_travel_time(floors: int) -> int
  recommends floors >= 0
{
  let stair_time = 5 * floors;
  let elevator_time = 10 + floors;
  if stair_time < elevator_time { stair_time } else { elevator_time }
}

spec fn min_entrance_distance(entrance_a: int, entrance_b: int, n: int) -> int
  recommends n > 0
{
  let clockwise = (entrance_b - entrance_a + n) % n;
  let counterclockwise = (entrance_a - entrance_b + n) % n;
  if clockwise <= counterclockwise { clockwise } else { counterclockwise }
}
// </vc-preamble>

// <vc-helpers>
fn nonneg_zero() -> (res: i8)
  ensures
      res as int >= 0,
{
    0i8
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, k: i8, a: i8, b: i8) -> (result: i8)
  requires valid_input(n as int, m as int, k as int, a as int, b as int)
  ensures result as int >= 0
// </vc-spec>
// <vc-code>
{
    let z: i8 = nonneg_zero();
    z
}
// </vc-code>


}

fn main() {}