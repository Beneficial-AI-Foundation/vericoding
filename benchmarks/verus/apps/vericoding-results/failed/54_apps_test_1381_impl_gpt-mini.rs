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
/* helper modified by LLM (iteration 5): lemma proving properties of min_packs_needed */
proof fn min_packs_props(k: int, n: int, s: int, p: int)
    requires
        k >= 1,
        n >= 1,
        s >= 1,
        p >= 1,
    ensures
        min_packs_needed(k, n, s, p) >= 1,
        min_packs_needed(k, n, s, p) * p >= total_sheets_needed(k, n, s),
        (min_packs_needed(k, n, s, p) - 1) * p < total_sheets_needed(k, n, s),
{
    proof {
        let ts = total_sheets_needed(k, n, s);
        let m = ts + p - 1;
        let q = m / p;
        let r = m % p;
        // unfold definition
        assert(min_packs_needed(k, n, s, p) == q);
        // division remainder properties
        assert(m == q * p + r);
        assert(0 <= r && r < p);
        // q * p = m - r >= m - (p - 1) = ts
        assert(q * p == m - r);
        assert(m - r == ts + (p - 1) - r);
        assert((p - 1) - r >= 0);
        assert(q * p >= ts);
        // (q - 1) * p = q*p - p < ts
        assert((q - 1) * p == q * p - p);
        assert(q * p - p == m - r - p);
        assert(m - r - p == ts - 1 - r);
        assert(ts - 1 - r < ts);
        // show q >= 1: m = ts + p - 1 >= p because ts >= 1
        assert(m >= p);
        assert(q >= 1);
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
  /* code modified by LLM (iteration 5): compute result and prove correctness using lemma helper */
  let sheets_per: i32 = (n + s - 1) / s;
  let total: i32 = k * sheets_per;
  let result: i32 = (total + p - 1) / p;
  proof {
    let k_i: int = k as int;
    let n_i: int = n as int;
    let s_i: int = s as int;
    let p_i: int = p as int;
    assert(sheets_per as int == sheets_per_person(n_i, s_i));
    assert(total as int == total_sheets_needed(k_i, n_i, s_i));
    assert(result as int == min_packs_needed(k_i, n_i, s_i, p_i));
    min_packs_props(k_i, n_i, s_i, p_i);
  }
  result
}

// </vc-code>


}

fn main() {}