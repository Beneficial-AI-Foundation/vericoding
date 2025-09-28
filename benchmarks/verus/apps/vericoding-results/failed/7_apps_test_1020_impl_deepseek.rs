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
/* helper modified by LLM (iteration 5): fixed lemma preconditions and ensures clauses */
proof fn lemma_compute_sum_decreases(w: int, h: int, k: int)
    requires
        k > 0,
        w >= 3,
        h >= 3,
    ensures
        compute_sum(w, h, k) == perimeter(w, h) + compute_sum(w - 4, h - 4, k - 1)
{
    reveal(compute_sum);
}

proof fn lemma_perimeter_nonnegative(w: int, h: int)
    requires
        w >= 3,
        h >= 3,
    ensures
        perimeter(w, h) >= 0
{
}

proof fn lemma_valid_input_recursive(w: int, h: int, k: int)
    requires
        w >= 3,
        h >= 3,
        k > 0,
        w - 4 >= 3,
        h - 4 >= 3,
    ensures
        valid_input(w - 4, h - 4, k - 1)
{
}

proof fn lemma_compute_sum_zero_case(w: int, h: int, k: int)
    requires
        k <= 0,
    ensures
        compute_sum(w, h, k) == 0
{
    reveal(compute_sum);
}
// </vc-helpers>

// <vc-spec>
fn gild_cells(w: i8, h: i8, k: i8) -> (result: i8)
    requires valid_input(w as int, h as int, k as int)
    ensures result as int == compute_sum(w as int, h as int, k as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed arithmetic operations and strengthened loop conditions */
{
    let mut sum: i8 = 0;
    let mut current_w: i8 = w;
    let mut current_h: i8 = h;
    let mut remaining_k: i8 = k;
    
    while remaining_k > 0
        invariant
            valid_input(current_w as int, current_h as int, remaining_k as int),
            sum as int + compute_sum(current_w as int, current_h as int, remaining_k as int) == compute_sum(w as int, h as int, k as int),
            remaining_k >= 0,
            current_w >= 3,
            current_h >= 3,
            current_w <= 100,
            current_h <= 100
        decreases remaining_k as int
    {
        proof {
            lemma_perimeter_nonnegative(current_w as int, current_h as int);
            lemma_valid_input_recursive(current_w as int, current_h as int, remaining_k as int);
            lemma_compute_sum_decreases(current_w as int, current_h as int, remaining_k as int);
        }
        
        let two: i8 = 2;
        let four: i8 = 4;
        let p1 = current_w.checked_mul(two).unwrap();
        let h_minus_2 = current_h.checked_sub(two).unwrap();
        let p2 = h_minus_2.checked_mul(two).unwrap();
        let p = p1.checked_add(p2).unwrap();
        sum = sum.checked_add(p).unwrap();
        current_w = current_w.checked_sub(four).unwrap();
        current_h = current_h.checked_sub(four).unwrap();
        remaining_k = remaining_k.checked_sub(1).unwrap();
    }
    
    proof {
        lemma_compute_sum_zero_case(current_w as int, current_h as int, remaining_k as int);
    }
    
    sum
}
// </vc-code>


}

fn main() {}