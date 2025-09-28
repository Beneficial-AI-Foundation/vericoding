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
    let mut result: i8 = 0;
    let mut ww = w;
    let mut hh = h;
    let mut kk = k;
    proof {
        assume(k >= 0);
    }
    while kk > 0
        invariant
            kk as int <= k as int,
            kk as int >= 0,
            result as int == compute_sum(w as int, h as int, k as int) - compute_sum(ww as int, hh as int, kk as int)
        decreases kk as int
    {
        result = result + (ww * 2 + (hh - 2) * 2);
        ww = ww - 4;
        hh = hh - 4;
        kk = kk - 1;
    }
    result
}
// </vc-code>


}

fn main() {}