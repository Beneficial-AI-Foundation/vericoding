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
    let ghost m_spec: int = m as int;
    let ghost b_spec: int = b as int;

    if m_spec == 0 {
        return 0i8;
    }

    let mut max_val: int = -1;
    let mut k: int = 0;

    while (k * m_spec) <= b_spec
        invariant 
            0 <= k,
            max_val == -1 || (forall|prev_k: int| 0 <= prev_k < k && valid_rectangle_corner(prev_k, m_spec, b_spec) ==> max_val >= rectangle_value(prev_k, m_spec, b_spec)),
            max_val == -1 || (exists|prev_k: int| 0 <= prev_k < k && valid_rectangle_corner(prev_k, m_spec, b_spec) && max_val == rectangle_value(prev_k, m_spec, b_spec)),
            k <= b_spec + 1
        decreases (b_spec - k * m_spec) + 1
    {
        if valid_rectangle_corner(k, m_spec, b_spec) {
            let current_value = rectangle_value(k, m_spec, b_spec);
            if max_val == -1 || current_value > max_val {
                max_val = current_value;
            }
        }
        k = k + 1;
    }

    if max_val == -1 {
        0i8
    } else {
        max_val as i8
    }
}
// </vc-code>


}

fn main() {}