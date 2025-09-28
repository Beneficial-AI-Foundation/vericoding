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
/* helper modified by LLM (iteration 5): [no_change] */
proof fn lemma_compute_sum_recurrence(w: int, h: int, k: int)
    requires
        k > 0,
        w >= 3 + 4 * (k - 1),
        h >= 3 + 4 * (k - 1),
        w - 4 * (k - 1) >= 3,
        h - 4 * (k - 1) >= 3,
        w >= 3,
        h >= 3
    ensures
        compute_sum(w, h, k) == perimeter(w, h) + compute_sum(w - 4, h - 4, k - 1)
    decreases k
{
    if k == 1 {
        assert(compute_sum(w, h, 1) == perimeter(w, h) + compute_sum(w - 4, h - 4, 0));
    } else {
        lemma_compute_sum_recurrence(w - 4, h - 4, k - 1);
        assert(compute_sum(w, h, k) == perimeter(w, h) + compute_sum(w - 4, h - 4, k - 1));
    }
}
// </vc-helpers>

// <vc-spec>
fn gild_cells(w: i8, h: i8, k: i8) -> (result: i8)
    requires valid_input(w as int, h as int, k as int)
    ensures result as int == compute_sum(w as int, h as int, k as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [Replaced int conversions in `current_perimeter` computation with `as i8` to avoid ghost code errors, and removed `h_by_val` macro calls] */
{
    let mut current_w: i8 = w;
    let mut current_h: i8 = h;
    let mut current_k: i8 = k;
    let mut total_gilded_cells: i8 = 0;

    // Ghost variables for reasoning about int values
    let mut ghost_current_w_int: Ghost<int> = Ghost(w as int);
    let mut ghost_current_h_int: Ghost<int> = Ghost(h as int);
    let mut ghost_current_k_int: Ghost<int> = Ghost(k as int);
    let mut ghost_total_gilded_cells_int: Ghost<int> = Ghost(0);

    while current_k > 0
        invariant
            current_w as int == ghost_current_w_int@,
            current_h as int == ghost_current_h_int@,
            current_k as int == ghost_current_k_int@,
            total_gilded_cells as int == ghost_total_gilded_cells_int@,

            ghost_current_w_int@ >= 3,
            ghost_current_h_int@ >= 3,
            ghost_current_k_int@ >= 0,
            ghost_current_k_int@ <= k as int,
            (w as int - 4 * (k as int - ghost_current_k_int@)) == ghost_current_w_int@,
            (h as int - 4 * (k as int - ghost_current_k_int@)) == ghost_current_h_int@,
            ghost_total_gilded_cells_int@ == compute_sum(w as int, h as int, k as int) - compute_sum(ghost_current_w_int@, ghost_current_h_int@, ghost_current_k_int@)
        decreases current_k
    {
        proof {
            let current_w_int = ghost_current_w_int@;
            let current_h_int = ghost_current_h_int@;
            let current_k_int = ghost_current_k_int@;
            let total_gilded_cells_int = ghost_total_gilded_cells_int@;

            if current_k_int > 0 {
                assert(w as int - 4 * k as int >= 3);
                assert(current_k_int <= k as int);
                assert(k as int - current_k_int >= 0);
                assert(w as int - 4 * (k as int - current_k_int) >= w as int - 4 * k as int);
                assert(w as int - 4 * (k as int - current_k_int) >= 3);
                assert(h as int - 4 * (k as int - current_k_int) >= 3);
                assert((current_w_int - 4) >= 3 || current_k_int == 1);
                assert((current_h_int - 4) >= 3 || current_k_int == 1);
            }
            lemma_compute_sum_recurrence(current_w_int, current_h_int, current_k_int);

            let current_perimeter_val_int = current_w_int * 2 + (current_h_int - 2) * 2;
            assert(current_perimeter_val_int >= 0 && current_perimeter_val_int <= 255);
            ghost_total_gilded_cells_int = Ghost(total_gilded_cells_int + current_perimeter_val_int);

            let next_current_w_int = current_w_int - 4;
            assert(next_current_w_int >= 0 && next_current_w_int <= 127);
            ghost_current_w_int = Ghost(next_current_w_int);

            let next_current_h_int = current_h_int - 4;
            assert(next_current_h_int >= 0 && next_current_h_int <= 127);
            ghost_current_h_int = Ghost(next_current_h_int);

            ghost_current_k_int = Ghost(current_k_int - 1);
        }

        let current_perimeter = (current_w as i16 * 2 + (current_h as i16 - 2) * 2) as i8;
        total_gilded_cells = total_gilded_cells + current_perimeter;
        current_w = current_w - 4;
        current_h = current_h - 4;
        current_k = current_k - 1;
    }

    total_gilded_cells
}
// </vc-code>


}

fn main() {}