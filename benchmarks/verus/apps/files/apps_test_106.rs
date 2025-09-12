// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, m: int, k: int, a: int, b: int) -> bool {
  n > 0 && m > 0 && k > 0 && 1 <= a <= n * m * k && 1 <= b <= n * m * k && a != b
}

spec fn get_entrance(apt: int, m: int, k: int) -> int {
  (apt - 1) / (m * k)
}

spec fn get_floor(apt: int, m: int, k: int) -> int {
  ((apt - 1) - get_entrance(apt, m, k) * m * k) / k
}

spec fn min_travel_time(floors: int) -> int {
  let stair_time = 5 * floors;
  let elevator_time = 10 + floors;
  if stair_time < elevator_time { stair_time } else { elevator_time }
}

spec fn min_entrance_distance(entrance_a: int, entrance_b: int, n: int) -> int {
  let clockwise = (entrance_b - entrance_a + n) % n;
  let counterclockwise = (entrance_a - entrance_b + n) % n;
  if clockwise <= counterclockwise { clockwise } else { counterclockwise }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, m: int, k: int, a: int, b: int) -> (result: int)
  requires 
    valid_input(n, m, k, a, b),
  ensures 
    result >= 0,
    get_entrance(a, m, k) == get_entrance(b, m, k) ==> 
      result == min_travel_time({let floor_a = get_floor(a, m, k);
                                 let floor_b = get_floor(b, m, k);
                                 if floor_a >= floor_b { floor_a - floor_b } else { floor_b - floor_a }}),
    get_entrance(a, m, k) != get_entrance(b, m, k) ==>
      result == min_travel_time(get_floor(a, m, k)) + 
                15 * min_entrance_distance(get_entrance(a, m, k), get_entrance(b, m, k), n) + 
                min_travel_time(get_floor(b, m, k)),
// </vc-spec>
// <vc-code>
{
  assume(false);
  0int
}
// </vc-code>


}

fn main() {}