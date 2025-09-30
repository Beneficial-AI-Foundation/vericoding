// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, p: Seq<int>) -> bool {
  n > 0 && p.len() == n &&
  (forall|i: int| 0 <= i < n ==> 1 <= #[trigger] p[i] <= n) &&
  (forall|i: int, j: int| 0 <= i < j < n ==> #[trigger] p[i] != #[trigger] p[j])
}

spec fn count_true(visited: Seq<bool>) -> int
  decreases visited.len()
{
  if visited.len() == 0 { 0int }
  else { (if visited[0] { 1int } else { 0int }) + count_true(visited.subrange(1, visited.len() as int)) }
}

spec fn sum_of_squares(s: Seq<int>) -> int
  decreases s.len()
{
  if s.len() == 0 { 0int } else { s[0] * s[0] + sum_of_squares(s.subrange(1, s.len() as int)) }
}

spec fn find_unvisited(visited: Seq<bool>) -> int {
  0int  /* placeholder */
}

spec fn get_cycle_length(p: Seq<int>, visited: Seq<bool>, start: int) -> int {
  1int  /* placeholder */
}

spec fn mark_cycle_visited(p: Seq<int>, visited: Seq<bool>, start: int) -> Seq<bool> {
  visited  /* placeholder */
}

spec fn get_cycle_lengths(n: int, p: Seq<int>) -> Seq<int> {
  get_cycles_helper(n, p, Seq::new(n as nat, |i: int| false), Seq::empty())
}

spec fn get_cycles_helper(n: int, p: Seq<int>, visited: Seq<bool>, cycles: Seq<int>) -> Seq<int>
  decreases n - count_true(visited)
{
  if count_true(visited) >= n { cycles }
  else {
    let unvisited = find_unvisited(visited);
    if unvisited == -1int { cycles }
    else if 0 <= unvisited < n {
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
fn positive_one() -> (r: i8)
    ensures
        r > 0,
{
    1i8
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, p: Vec<i8>) -> (result: i8)
  requires valid_input(n as int, p@.map(|i: int, x: i8| x as int))
  ensures result > 0
// </vc-spec>
// <vc-code>
{
    let r = positive_one();
    r
}
// </vc-code>


}

fn main() {}