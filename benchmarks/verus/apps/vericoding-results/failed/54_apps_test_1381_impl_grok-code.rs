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
    /* code modified by LLM (iteration 5): switched to u64 arithmetic to prevent overflow errors, maintaining proof that matches spec */
    let n_as_u64 = n as u64;
    let s_as_u64 = s as u64;
    let k_as_u64 = k as u64;
    let p_as_u64 = p as u64;
    let sheets_per = (n_as_u64 + s_as_u64 - 1) / s_as_u64;
    let total_sheets = k_as_u64 * sheets_per;
    let result_u64 = (total_sheets + p_as_u64 - 1) / p_as_u64;
    proof {
        let k_int = k as int;
        let n_int = n as int;
        let s_int = s as int;
        let p_int = p as int;
        let sheets_per_spec = sheets_per_person(n_int, s_int);
        let total_spec = total_sheets_needed(k_int, n_int, s_int);
        let res_spec = min_packs_needed(k_int, n_int, s_int, p_int);
        assert(sheets_per == sheets_per_spec);
        assert(total_sheets == total_spec);
        assert(result_u64 == res_spec);
        assert(result_u64 <= 2147483647);
        assert(result_u64 >= 1);
    }
    (result_u64 as i32)
}
// </vc-code>


}

fn main() {}