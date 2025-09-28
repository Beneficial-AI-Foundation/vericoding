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
/* helper modified by LLM (iteration 5): replaced saturating_mul with regular multiplication */
fn exec_f(x: i64, y: i64) -> i64 {
    let x_plus_1 = x + 1;
    let y_plus_1 = y + 1;
    
    let term1 = x * x_plus_1 * y_plus_1;
    let term2 = y * y_plus_1 * x_plus_1;
    
    (term1 + term2) / 2
}
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
/* code modified by LLM (iteration 5): replaced saturating_mul with regular multiplication */
{
    let m_exec = m as i64;
    let b_exec = b as i64;
    let mut max_val: i64 = 0;
    let mut k: i64 = 0;
    
    // Initialize max_val with f(0, b)
    max_val = exec_f(0, b_exec);
    k = 1;
    
    while k <= b_exec
        invariant
            0 <= k as int <= (b as int) + 1,
            forall|i: int| 0 <= i < k as int ==> (max_val as int) >= #[trigger] f(i * (m as int), (b as int) - i),
            exists|i: int| 0 <= i < k as int && (max_val as int) == #[trigger] f(i * (m as int), (b as int) - i),
        decreases (b as int + 1) - (k as int),
    {
        let k_m = k * m_exec;
        let b_minus_k = b_exec - k;
        let candidate = exec_f(k_m, b_minus_k);
        
        if candidate > max_val {
            max_val = candidate;
        }
        k = k + 1;
    }
    
    // Ensure result fits in i8 range
    if max_val > i8::MAX as i64 {
        i8::MAX
    } else if max_val < i8::MIN as i64 {
        i8::MIN
    } else {
        max_val as i8
    }
}
// </vc-code>


}

fn main() {}