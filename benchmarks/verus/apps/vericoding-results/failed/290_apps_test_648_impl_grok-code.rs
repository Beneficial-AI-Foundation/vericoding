// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(m: int, b: int) -> bool {
  1 <= m <= 1000 && 1 <= b <= 10000
}

spec fn f(x: int, y: int) -> int {
  (x * (x + 1) * (y + 1) + y * (y + 1) * (x + 1)) / 2
}

spec fn valid_rectangle_corner(k: int, m: int, b: int) -> bool {
  0 <= k && b - k >= 0
}

spec fn rectangle_value(k: int, m: int, b: int) -> int {
  f(k * m, b - k)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(m: i8, b: i8) -> (result: i8)
  requires 
    valid_input(m as int, b as int)
  ensures 
    result as int >= -1,
    forall|k: int| valid_rectangle_corner(k, m as int, b as int) ==> result as int >= rectangle_value(k, m as int, b as int),
    exists|k: int| valid_rectangle_corner(k, m as int, b as int) && result as int == rectangle_value(k, m as int, b as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by removing #[trigger] from invariant forall, added type casts, and added assert for safe i8 cast */
    let mut MAX: i64 = (((0i64 * (m as i64)) * ((0i64 * (m as i64)) + 1) * ((b as i64) - 0 + 1) + ((b as i64) - 0) * (((b as i64) - 0) + 1) * ((0i64 * (m as i64)) + 1)) / 2);
    let mut max_k: i64 = 0;
    let mut k: i64 = 1;
    while k <= (b as i64)
        invariant
            1 <= k <= b as int + 1,
            0 <= max_k < k <= b as int + 1,
            MAX == rectangle_value(max_k as int, m as int, b as int) as i64,
            forall |k2: int| 0 <= k2 < k ==> MAX as int >= rectangle_value(k2, m as int, b as int),
        decreases (b as int - k + 1)
    {
        let val: i64 = (((k * (m as i64)) * ((k * (m as i64)) + 1) * ((b as i64) - k + 1) + ((b as i64) - k) * (((b as i64) - k) + 1) * ((k * (m as i64)) + 1)) / 2);
        if val > MAX {
            MAX = val;
            max_k = k;
        }
        k += 1;
    }
    assert(MAX <= 127);
    (MAX as i8)
}
// </vc-code>


}

fn main() {}