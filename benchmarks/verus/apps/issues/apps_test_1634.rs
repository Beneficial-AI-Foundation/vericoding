// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_costs(c: &[int]) -> bool {
  c.len() == 4 &&
  c[0] >= 1 && c[1] >= 1 && c[2] >= 1 && c[3] >= 1 &&
  c[0] <= 1000 && c[1] <= 1000 && c[2] <= 1000 && c[3] <= 1000
}

spec fn valid_rides(rides: &[int]) -> bool {
  rides.len() >= 1 && rides.len() <= 1000 &&
  forall|i: int| #![trigger rides[i]] 0 <= i < rides.len() ==> 0 <= rides[i] <= 1000
}

spec fn sum_array(arr: Seq<int>) -> int
  decreases arr.len(),
{
  if arr.len() == 0 { 
    0 
  } else { 
    arr[0] + sum_array(arr.drop_first()) 
  }
}

spec fn optimized_cost(rides: Seq<int>, individual_cost: int, unlimited_cost: int) -> int {
  let initial_cost = sum_array(rides) * individual_cost;
  min_with_unlimited(rides, initial_cost, individual_cost, unlimited_cost, 0)
}

spec fn min_with_unlimited(rides: Seq<int>, current_cost: int, individual_cost: int, unlimited_cost: int, index: int) -> int
  decreases rides.len() - index,
{
  if index >= rides.len() { 
    current_cost 
  } else {
    let new_cost = current_cost - rides[index] * individual_cost + unlimited_cost;
    let updated_cost = if new_cost < current_cost && new_cost >= 0 { new_cost } else { current_cost };
    min_with_unlimited(rides, updated_cost, individual_cost, unlimited_cost, index + 1)
  }
}

spec fn min5(a: int, b: int, c: int, d: int, e: int) -> int {
  let min_ab = if a <= b { a } else { b };
  let min_cd = if c <= d { c } else { d };
  let min_abcd = if min_ab <= min_cd { min_ab } else { min_cd };
  if min_abcd <= e { min_abcd } else { e }
}

spec fn correct_result(c: &[int], a: &[int], b: &[int], result: int) -> bool {
  result == min5(optimized_cost(a@, c[0], c[1]) + optimized_cost(b@, c[0], c[1]),
                 optimized_cost(a@, c[0], c[1]) + c[2],
                 optimized_cost(b@, c[0], c[1]) + c[2],
                 c[2] + c[2],
                 c[3])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(c: &Vec<i8>, a: &Vec<i8>, b: &Vec<i8>) -> (result: i8)
  requires 
    c.len() == 4,
    c@[0] as int >= 1 && c@[1] as int >= 1 && c@[2] as int >= 1 && c@[3] as int >= 1,
    c@[0] as int <= 1000 && c@[1] as int <= 1000 && c@[2] as int <= 1000 && c@[3] as int <= 1000,
    a.len() >= 1 && a.len() <= 1000,
    b.len() >= 1 && b.len() <= 1000,
    forall|i: int| #![trigger a@[i]] 0 <= i < a.len() ==> 0 <= a@[i] as int <= 1000,
    forall|i: int| #![trigger b@[i]] 0 <= i < b.len() ==> 0 <= b@[i] as int <= 1000,
  ensures 
    result >= 0,
    result as int <= min5(sum_array(a@.map(|_, x: i8| x as int)) * (c@[0] as int) + sum_array(b@.map(|_, x: i8| x as int)) * (c@[0] as int), 
                  sum_array(a@.map(|_, x: i8| x as int)) * (c@[0] as int) + (c@[2] as int),
                  sum_array(b@.map(|_, x: i8| x as int)) * (c@[0] as int) + (c@[2] as int),
                  (c@[2] as int) + (c@[2] as int),
                  c@[3] as int),
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}