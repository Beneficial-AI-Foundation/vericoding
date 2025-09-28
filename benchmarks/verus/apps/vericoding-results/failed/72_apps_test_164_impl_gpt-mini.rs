// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(y1: int, y2: int, y_w: int, x_b: int, y_b: int, r: int) -> bool {
    y1 < y2 < y_w &&
    y_b + r < y_w &&
    2 * r < y2 - y1 &&
    x_b > 0 && y_b > 0 && r > 0 &&
    2 * (y_w - r) - y1 - y_b - r != 0
}

spec fn compute_w(y_w: int, r: int) -> int {
    y_w - r
}

spec fn compute_new_y1(y_w: int, r: int, y1: int, y_b: int) -> int {
    2 * (y_w - r) - y1 - y_b - r
}

spec fn compute_new_y2(y_w: int, r: int, y2: int, y_b: int) -> int {
    2 * (y_w - r) - y2 - y_b
}

spec fn compute_left_side(x_b: int, new_y1: int, new_y2: int) -> int {
    x_b * x_b * (new_y2 - new_y1) * (new_y2 - new_y1)
}

spec fn compute_right_side(x_b: int, new_y1: int, r: int) -> int {
    (new_y1 * new_y1 + x_b * x_b) * r * r
}

spec fn is_impossible(y1: int, y2: int, y_w: int, x_b: int, y_b: int, r: int) -> bool
    recommends valid_input(y1, y2, y_w, x_b, y_b, r)
{
    let w = compute_w(y_w, r);
    let new_y1 = compute_new_y1(y_w, r, y1, y_b);
    let new_y2 = compute_new_y2(y_w, r, y2, y_b);
    let left_side = compute_left_side(x_b, new_y1, new_y2);
    let right_side = compute_right_side(x_b, new_y1, r);
    left_side <= right_side
}

spec fn compute_solution(y1: int, y2: int, y_w: int, x_b: int, y_b: int, r: int) -> int
    recommends 
        valid_input(y1, y2, y_w, x_b, y_b, r) &&
        !is_impossible(y1, y2, y_w, x_b, y_b, r)
{
    let w = compute_w(y_w, r);
    let new_y1 = compute_new_y1(y_w, r, y1, y_b);
    x_b * (new_y1 + y_b - w) / new_y1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): prove new_y1 is nonzero under valid_input */
fn new_y1_nonzero(y1: int, y2: int, y_w: int, x_b: int, y_b: int, r: int)
    requires
        valid_input(y1, y2, y_w, x_b, y_b, r),
    ensures
        compute_new_y1(y_w, r, y1, y_b) != 0,
{
    proof {
        assert(2 * (y_w - r) - y1 - y_b - r != 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(y1: i8, y2: i8, y_w: i8, x_b: i8, y_b: i8, r: i8) -> (result: i8)
    requires 
        valid_input(y1 as int, y2 as int, y_w as int, x_b as int, y_b as int, r as int)
    ensures 
        is_impossible(y1 as int, y2 as int, y_w as int, x_b as int, y_b as int, r as int) ==> result == -1,
        !is_impossible(y1 as int, y2 as int, y_w as int, x_b as int, y_b as int, r as int) ==> result as int == compute_solution(y1 as int, y2 as int, y_w as int, x_b as int, y_b as int, r as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): compute using i128 runtime arithmetic and prove divisor nonzero in proof */
    let y1_i128: i128 = y1 as i128;
    let y2_i128: i128 = y2 as i128;
    let y_w_i128: i128 = y_w as i128;
    let x_b_i128: i128 = x_b as i128;
    let y_b_i128: i128 = y_b as i128;
    let r_i128: i128 = r as i128;

    let w = y_w_i128 - r_i128;
    let new_y1 = 2 * (y_w_i128 - r_i128) - y1_i128 - y_b_i128 - r_i128;
    let new_y2 = 2 * (y_w_i128 - r_i128) - y2_i128 - y_b_i128;

    let diff = new_y2 - new_y1;
    let left_side = x_b_i128 * x_b_i128 * diff * diff;
    let right_side = (new_y1 * new_y1 + x_b_i128 * x_b_i128) * r_i128 * r_i128;

    if left_side <= right_side {
        -1
    } else {
        proof {
            let y1_spec: int = y1 as int;
            let y2_spec: int = y2 as int;
            let y_w_spec: int = y_w as int;
            let x_b_spec: int = x_b as int;
            let y_b_spec: int = y_b as int;
            let r_spec: int = r as int;
            new_y1_nonzero(y1_spec, y2_spec, y_w_spec, x_b_spec, y_b_spec, r_spec);
            let new_y1_spec: int = new_y1 as int;
            assert(new_y1_spec != 0);
        }
        let sol = x_b_i128 * (new_y1 + y_b_i128 - w) / new_y1;
        #[verifier::truncate]
        sol as i8
    }
}
// </vc-code>


}

fn main() {}