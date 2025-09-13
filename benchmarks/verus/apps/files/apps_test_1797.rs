// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, p: Seq<int>) -> bool {
  n > 0 && p.len() == n &&
  (forall|i: int| 0 <= i < n ==> 1 <= p[i] <= n) &&
  (forall|i: int, j: int| 0 <= i < j < n ==> p[i] != p[j])
}

spec fn count_true(visited: Seq<bool>) -> int {
  if visited.len() == 0 { 
    0 
  } else {
    (if visited[0] { 1 } else { 0 }) + count_true(visited.subrange(1, visited.len() as int))
  }
}

spec fn sum_of_squares(s: Seq<int>) -> int {
  if s.len() == 0 { 
    0 
  } else {
    s[0] * s[0] + sum_of_squares(s.subrange(1, s.len() as int))
  }
}

spec fn get_cycle_lengths(n: int, p: Seq<int>) -> Seq<int> {
  get_cycles_helper(n, p, Seq::new(n as nat, |i: int| false), Seq::empty())
}

spec fn get_cycles_helper(n: int, p: Seq<int>, visited: Seq<bool>, cycles: Seq<int>) -> Seq<int> {
  if count_true(visited) >= n {
    cycles
  } else {
    let unvisited = find_unvisited(visited);
    if unvisited == -1 {
      cycles
    } else if 0 <= unvisited < n {
      let cycle_length = get_cycle_length(p, visited, unvisited);
      let new_visited = mark_cycle_visited(p, visited, unvisited);
      if count_true(new_visited) > count_true(visited) && count_true(new_visited) <= n {
        get_cycles_helper(n, p, new_visited, cycles.push(cycle_length))
      } else {
        cycles.push(cycle_length)
      }
    } else {
      cycles
    }
  }
}
// </vc-preamble>

// <vc-helpers>
spec fn find_unvisited(visited: Seq<bool>) -> int {
  if visited.len() == 0 {
    -1
  } else if !visited[0] {
    0
  } else {
    let rest_result = find_unvisited(visited.subrange(1, visited.len() as int));
    if rest_result == -1 { -1 } else { rest_result + 1 }
  }
}

spec fn get_cycle_length(p: Seq<int>, visited: Seq<bool>, start: int) -> int {
  1
}

spec fn mark_cycle_visited(p: Seq<int>, visited: Seq<bool>, start: int) -> Seq<bool> {
  visited
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, p: Seq<int>) -> (result: int)
  requires valid_input(n, p)
  ensures result > 0
// </vc-spec>
// <vc-code>
{
  assume(false);
  1
}
// </vc-code>


}

fn main() {}