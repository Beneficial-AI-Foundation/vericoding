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
fn gcd_exec(a: i128, b: i128) -> (res: i128)
    requires
        a >= 0,
        b >= 0,
    ensures
        res as int == gcd(a as int, b as int),
        res >= 0,
    decreases b as int
{
    if b == 0 {
        a
    } else {
        let r = a % b;
        gcd_exec(b, r)
    }
}

fn can_avoid_exec(r: i8, b: i8, k: i8) -> (res: bool)
    requires
        valid_input(r as int, b as int, k as int),
    ensures
        res == can_avoid_consecutive(r as int, b as int, k as int),
{
    let ri: i128 = r as i128;
    let bi: i128 = b as i128;
    let ai: i128 = if ri <= bi { ri } else { bi };
    let bvi: i128 = if ri <= bi { bi } else { ri };
    let n: i128 = gcd_exec(ai, bvi);
    let mc: i128 = -((n - bvi) / ai);
    let res_exec: bool = mc < (k as i128);
    proof {
        assert(valid_input(r as int, b as int, k as int));
        assert(can_avoid_consecutive(r as int, b as int, k as int)
               == (valid_input(r as int, b as int, k as int) && max_consecutive_same_color(r as int, b as int) < k as int));
        assert(can_avoid_consecutive(r as int, b as int, k as int)
               == (max_consecutive_same_color(r as int, b as int) < k as int));
        let ai_int = if (r as int) <= (b as int) { r as int } else { b as int };
        let bvi_int = if (r as int) <= (b as int) { b as int } else { r as int };
        assert(ai as int == ai_int);
        assert(bvi as int == bvi_int);
        assert(n as int == gcd(ai_int, bvi_int));
        let mc_int = -(((n as int) - bvi_int) / ai_int);
        assert(mc as int == mc_int);
        assert(res_exec == (mc_int < (k as int)));
    }
    res_exec
}
// </vc-helpers>

// <vc-spec>
fn solve(r: i8, b: i8, k: i8) -> (result: String)
  requires valid_input(r as int, b as int, k as int)
  ensures result@ == (if can_avoid_consecutive(r as int, b as int, k as int) { "OBEY"@ } else { "REBEL"@ })
// </vc-spec>
// <vc-code>
{
    let obey = can_avoid_exec(r, b, k);
    if obey {
        String::from("OBEY")
    } else {
        String::from("REBEL")
    }
}
// </vc-code>


}

fn main() {}