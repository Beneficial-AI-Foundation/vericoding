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
    let mut total: int = 0;
    let mut current_w = w as int;
    let mut current_h = h as int;
    let mut layers = k as int;
    while layers > 0
        invariant 
            layers >= 0,
            current_w == (w as int) - 4 * ((k as int) - layers),
            current_h == (h as int) - 4 * ((k as int) - layers),
            total + compute_sum(current_w, current_h, layers) == compute_sum(w as int, h as int, k as int),
        decreases layers
    {
        let p = 2 * current_w + 2 * (current_h - 2);
        total += p;
        current_w -= 4;
        current_h -= 4;
        layers -= 1;
    }
    total as i8
}
// </vc-code>


}

fn main() {}