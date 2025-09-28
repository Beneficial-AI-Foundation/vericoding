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
    /* code modified by LLM (iteration 5): Fixed naming conflict by renaming local variable */
    
    // Calculate sheets per person
    let sheets_per_person_val = (n + s - 1) / s;
    
    // Prove that sheets_per_person_val is bounded
    proof {
        // Since n <= 10000 and s >= 1, we have:
        // sheets_per_person_val = (n + s - 1) / s <= (n + s - 1) / 1 = n + s - 1
        // Since n <= 10000 and s <= 10000, sheets_per_person_val <= 10000 + 10000 - 1 = 19999
        assert(n <= 10000);
        assert(s <= 10000);
        assert(n + s - 1 <= 19999);
        assert(sheets_per_person_val <= n + s - 1);
        assert(sheets_per_person_val <= 19999);
    }
    
    // Calculate total sheets with explicit i64 to avoid overflow
    let k_i64: i64 = k as i64;
    let sheets_per_person_i64: i64 = sheets_per_person_val as i64;
    let total_sheets_i64: i64 = k_i64 * sheets_per_person_i64;
    
    proof {
        // k <= 10000 and sheets_per_person_val <= 19999
        // So total_sheets <= 10000 * 19999 = 199,990,000 < i32::MAX
        assert(k_i64 <= 10000);
        assert(sheets_per_person_i64 <= 19999);
        assert(total_sheets_i64 <= 199990000);
        assert(total_sheets_i64 <= i32::MAX as i64);
    }
    
    let total_sheets: i32 = total_sheets_i64 as i32;
    
    // Calculate result
    let result = (total_sheets + p - 1) / p;
    
    // Verify the result satisfies the postcondition
    assert(sheets_per_person_val as int == sheets_per_person(n as int, s as int));
    assert(total_sheets as int == total_sheets_needed(k as int, n as int, s as int));
    assert(result as int == min_packs_needed(k as int, n as int, s as int, p as int));
    assert(result >= 1);
    
    result
}
// </vc-code>


}

fn main() {}