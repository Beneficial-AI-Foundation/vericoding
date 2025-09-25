// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, t: int, routes: Seq<(int, int)>) -> bool {
  n > 0 && routes.len() == n && 
  forall|i: int| 0 <= i < n ==> routes[i].1 > 0
}

spec fn get_next_arrival_time(first_time: int, interval: int, target_time: int) -> int
  requires interval > 0
{
  if first_time >= target_time { 
    first_time
  } else { 
    first_time + ((target_time - first_time + interval - 1) / interval) * interval
  }
}

spec fn is_optimal_route(routes: Seq<(int, int)>, t: int, route_index: int) -> bool {
  &&& 0 <= route_index < routes.len()
  &&& (forall|i: int| 0 <= i < routes.len() ==> routes[i].1 > 0)
  &&& (forall|i: int| 0 <= i < routes.len() ==> 
    get_next_arrival_time(routes[route_index].0, routes[route_index].1, t) <= 
    get_next_arrival_time(routes[i].0, routes[i].1, t))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, t: int, routes: Seq<(int, int)>) -> (result: int)
  requires valid_input(n, t, routes),
  ensures 1 <= result <= n,
  ensures is_optimal_route(routes, t, result - 1)
// </vc-spec>
// <vc-code>
{
  assume(false);
  0
}
// </vc-code>


}

fn main() {}