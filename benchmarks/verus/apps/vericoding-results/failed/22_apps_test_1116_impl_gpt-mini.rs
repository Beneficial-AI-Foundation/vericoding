// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn gcd(a: int, b: int) -> int
  decreases b when a > 0 && b >= 0
{
  if b == 0 { a } else { gcd(b, a % b) }
}

spec fn valid_input(r: int, b: int, k: int) -> bool {
  r > 0 && b > 0 && k > 0
}

spec fn max_consecutive_same_color(r: int, b: int) -> int {
  let a = if r <= b { r } else { b };
  let b_val = if r <= b { b } else { r };
  let n = gcd(a, b_val);
  -((n - b_val) / a)
}

spec fn can_avoid_consecutive(r: int, b: int, k: int) -> bool {
  valid_input(r, b, k) && max_consecutive_same_color(r, b) < k
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): exec gcd with spec correspondence */
fn gcd_i64(a_init: i64, b_init: i64) -> i64
    requires
        a_init >= 0,
        b_init >= 0,
    ensures
        (result as int) == gcd(a_init as int, b_init as int),
{
    let mut a = a_init;
    let mut b = b_init;
    while b != 0
        invariant
            a >= 0,
            b >= 0,
            gcd(a as int, b as int) == gcd(a_init as int, b_init as int),
        decreases
            b
    {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}
// </vc-helpers>

// <vc-spec>
fn solve(r: i8, b: i8, k: i8) -> (result: String)
  requires valid_input(r as int, b as int, k as int)
  ensures result@ == (if can_avoid_consecutive(r as int, b as int, k as int) { "OBEY"@ } else { "REBEL"@ })
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 3): compute gcd and decide result using gcd_i64, with proof linking to spec */
    let r_i64: i64 = r as i64;
    let b_i64: i64 = b as i64;
    let k_i64: i64 = k as i64;

    let a: i64 = if r_i64 <= b_i64 { r_i64 } else { b_i64 };
    let b_val: i64 = if r_i64 <= b_i64 { b_i64 } else { r_i64 };

    let n: i64 = gcd_i64(a, b_val);
    let maxc: i64 = -((n - b_val) / a);

    let res_str = if maxc < k_i64 {
        String::from_str("OBEY")
    } else {
        String::from_str("REBEL")
    };

    proof {
        assert((n as int) == gcd(a as int, b_val as int));

        let r_i: int = r as int;
        let b_i: int = b as int;
        let k_i: int = k as int;
        let a_g: int = if r_i <= b_i { r_i } else { b_i };
        let b_g: int = if r_i <= b_i { b_i } else { r_i };
        assert((maxc as int) == max_consecutive_same_color(a_g, b_g));

        if maxc < k_i64 {
            assert(can_avoid_consecutive(r_i, b_i, k_i));
            assert(res_str@ == "OBEY"@);
        } else {
            assert(!can_avoid_consecutive(r_i, b_i, k_i));
            assert(res_str@ == "REBEL"@);
        }
    }

    res_str
}
// </vc-code>


}

fn main() {}