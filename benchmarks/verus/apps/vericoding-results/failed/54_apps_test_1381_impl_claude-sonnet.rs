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
/* helper modified by LLM (iteration 5): removed proof blocks from helper functions */
proof fn sheets_per_person_positive(n: int, s: int)
    requires n >= 1, s >= 1
    ensures sheets_per_person(n, s) >= 1
{
    assert(n + s - 1 >= s);
    assert((n + s - 1) / s >= 1);
}

proof fn total_sheets_positive(k: int, n: int, s: int)
    requires k >= 1, n >= 1, s >= 1
    ensures total_sheets_needed(k, n, s) >= 1
{
    sheets_per_person_positive(n, s);
    assert(sheets_per_person(n, s) >= 1);
    assert(k >= 1);
    assert(k * sheets_per_person(n, s) >= 1);
}

proof fn min_packs_positive(k: int, n: int, s: int, p: int)
    requires k >= 1, n >= 1, s >= 1, p >= 1
    ensures min_packs_needed(k, n, s, p) >= 1
{
    total_sheets_positive(k, n, s);
    let total = total_sheets_needed(k, n, s);
    assert(total >= 1);
    assert(total + p - 1 >= p);
    assert((total + p - 1) / p >= 1);
}

proof fn division_ceiling_property(a: int, b: int)
    requires a >= 1, b >= 1
    ensures
        (a + b - 1) / b * b >= a,
        ((a + b - 1) / b - 1) * b < a
{
    let q = (a + b - 1) / b;
    let r = (a + b - 1) % b;
    assert(a + b - 1 == q * b + r);
    assert(0 <= r < b);
    assert(a == q * b + r - b + 1);
    assert(q * b >= a);
    if q > 1 {
        assert((q - 1) * b < a);
    }
}
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
    /* code modified by LLM (iteration 5): removed proof blocks from function body */
    let sheets_needed_per_person = (n + s - 1) / s;
    
    assert(n as int >= 1 && s as int >= 1);
    assert(sheets_needed_per_person as int == sheets_per_person(n as int, s as int));
    sheets_per_person_positive(n as int, s as int);
    assert(sheets_needed_per_person >= 1);
    assert(k as int <= 10000 && sheets_needed_per_person as int >= 1);
    assert(k as int * sheets_needed_per_person as int <= 10000 * 10000);
    
    let total_sheets = k * sheets_needed_per_person;
    
    assert(total_sheets as int == total_sheets_needed(k as int, n as int, s as int));
    total_sheets_positive(k as int, n as int, s as int);
    assert(total_sheets >= 1);
    assert(total_sheets as int + p as int - 1 <= 100000000 + 10000);
    
    let packs_needed = (total_sheets + p - 1) / p;
    
    min_packs_positive(k as int, n as int, s as int, p as int);
    division_ceiling_property(total_sheets as int, p as int);
    assert(packs_needed as int == min_packs_needed(k as int, n as int, s as int, p as int));
    assert(correct_result(packs_needed as int, k as int, n as int, s as int, p as int));
    
    packs_needed
}
// </vc-code>


}

fn main() {}