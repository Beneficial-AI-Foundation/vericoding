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
/* helper modified by LLM (iteration 3): [add exec helper and proof of non-negativity] */
#[verifier::spinoff_prover]
fn exec_rectangle_value(k: i32, m: i8, b: i8) -> (res: i64)
    requires
        valid_input(m as int, b as int),
        valid_rectangle_corner(k as int, m as int, b as int),
    ensures
        res == rectangle_value(k as int, m as int, b as int),
{
    let k_i64 = k as i64;
    let m_i64 = m as i64;
    let b_i64 = b as i64;

    let x = k_i64 * m_i64;
    let y = b_i64 - k_i64;
    
    let x_plus_1 = x + 1;
    let y_plus_1 = y + 1;
    let x_plus_y = x + y;
    
    let term1 = x_plus_1 * y_plus_1;
    let prod = term1 * x_plus_y;
    prod / 2
}

proof fn lemma_rectangle_value_ge_0(k: int, m: int, b: int)
    requires
        valid_input(m, b),
        valid_rectangle_corner(k, m, b),
    ensures
        rectangle_value(k, m, b) >= 0,
{
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
{
    /* code modified by LLM (iteration 3): [fix compilation errors and implement search loop] */
    ghost let m_int = m as int;
    ghost let b_int = b as int;

    assert(valid_rectangle_corner(0, m_int, b_int));
    
    let mut max_val_exec = exec_rectangle_value(0, m, b);
    ghost let mut best_k: int = 0;
    
    let mut k_exec: i32 = 1;
    let b_i32 = b as i32;

    while k_exec <= b_i32
        invariant
            1 <= k_exec <= b_i32 + 1,
            valid_input(m_int, b_int),
            b_i32 == b_int,
            valid_rectangle_corner(best_k, m_int, b_int),
            max_val_exec == rectangle_value(best_k, m_int, b_int),
            forall|i: int| 0 <= i < k_exec && valid_rectangle_corner(i, m_int, b_int) ==> max_val_exec >= rectangle_value(i, m_int, b_int),
        decreases b_i32 - k_exec
    {
        assert(valid_rectangle_corner(k_exec as int, m_int, b_int));
        let current_val = exec_rectangle_value(k_exec, m, b);

        if current_val > max_val_exec {
            max_val_exec = current_val;
            ghost { best_k = k_exec as int; }
        }
        k_exec = k_exec + 1;
    }

    max_val_exec as i8
}
// </vc-code>


}

fn main() {}