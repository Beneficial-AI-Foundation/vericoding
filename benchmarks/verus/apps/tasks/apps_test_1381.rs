// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(k: int, n: int, s: int, p: int) -> bool {
  k >= 1 && n >= 1 && s >= 1 && p >= 1 &&
  k <= 10000 && n <= 10000 && s <= 10000 && p <= 10000
}

spec fn sheets_per_person(n: int, s: int) -> int
  recommends s >= 1
{
  (n + s - 1) / s
}

spec fn total_sheets_needed(k: int, n: int, s: int) -> int
  recommends s >= 1
{
  k * sheets_per_person(n, s)
}

spec fn min_packs_needed(k: int, n: int, s: int, p: int) -> int
  recommends s >= 1 && p >= 1
{
  (total_sheets_needed(k, n, s) + p - 1) / p
}

spec fn correct_result(result: int, k: int, n: int, s: int, p: int) -> bool
  recommends s >= 1 && p >= 1
{
  result == min_packs_needed(k, n, s, p) &&
  result * p >= total_sheets_needed(k, n, s) &&
  (result - 1) * p < total_sheets_needed(k, n, s)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(k: i32, n: i32, s: i32, p: i32) -> (result: i32)
  requires
    valid_input(k as int, n as int, s as int, p as int),
  ensures
    result >= 1,
    correct_result(result as int, k as int, n as int, s as int, p as int),
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}