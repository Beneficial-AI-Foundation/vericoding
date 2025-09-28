// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(w: int, h: int, k: int) -> bool {
    w >= 3 && h >= 3 && w <= 100 && h <= 100 && 
    k >= 1 && k <= ((if w <= h { w } else { h }) + 1) / 4 &&
    w - 4 * k >= 3 && h - 4 * k >= 3
}

spec fn perimeter(w: int, h: int) -> int {
    w * 2 + (h - 2) * 2
}

spec fn compute_sum(w: int, h: int, k: int) -> int
    decreases k when k > 0
{
    if k <= 0 { 0 }
    else { 
        perimeter(w, h) + compute_sum(w - 4, h - 4, k - 1)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn gild_cells(w: i8, h: i8, k: i8) -> (result: i8)
    requires valid_input(w as int, h as int, k as int)
    ensures result as int == compute_sum(w as int, h as int, k as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): corrected ghost variable syntax */
    let ghost w_int = w as int;
    let ghost h_int = h as int;
    let ghost k_int = k as int;

    let mut w_curr = w as i32;
    let mut h_curr = h as i32;
    let mut k_curr = k as i32;
    let mut sum: i32 = 0;

    while k_curr > 0
        invariant
            k_curr >= 0,
            (w_curr as int) == w_int - 4 * (k_int - (k_curr as int)),
            (h_curr as int) == h_int - 4 * (k_int - (k_curr as int)),
            (sum as int) + compute_sum(w_curr as int, h_curr as int, k_curr as int) == compute_sum(w_int, h_int, k_int),
        decreases k_curr
    {
        proof {
            assert(compute_sum(w_curr as int, h_curr as int, k_curr as int) == 
                   perimeter(w_curr as int, h_curr as int) + 
                   compute_sum((w_curr - 4) as int, (h_curr - 4) as int, (k_curr - 1) as int));
        }
        
        let p = w_curr * 2 + (h_curr - 2) * 2;
        sum = sum + p;

        w_curr = w_curr - 4;
        h_curr = h_curr - 4;
        k_curr = k_curr - 1;
    }
    
    proof {
        assert(compute_sum(w as int, h as int, k as int) <= i8::MAX as int);
        assert(compute_sum(w as int, h as int, k as int) >= i8::MIN as int);
    }
    
    sum as i8
}
// </vc-code>


}

fn main() {}