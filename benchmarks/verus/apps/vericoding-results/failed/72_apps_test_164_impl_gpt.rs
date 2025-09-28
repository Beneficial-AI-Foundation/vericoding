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
/* helper modified by LLM (iteration 2): added i8-spec wrappers to avoid exec `as int` casts */
spec fn is_impossible_i8(y1: i8, y2: i8, y_w: i8, x_b: i8, y_b: i8, r: i8) -> bool {
    is_impossible(y1 as int, y2 as int, y_w as int, x_b as int, y_b as int, r as int)
}

/* helper modified by LLM (iteration 2): added i8-spec wrapper for compute_solution */
spec fn compute_solution_i8(y1: i8, y2: i8, y_w: i8, x_b: i8, y_b: i8, r: i8) -> int
    recommends
        valid_input(y1 as int, y2 as int, y_w as int, x_b as int, y_b as int, r as int) &&
        !is_impossible(y1 as int, y2 as int, y_w as int, x_b as int, y_b as int, r as int)
{
    compute_solution(y1 as int, y2 as int, y_w as int, x_b as int, y_b as int, r as int)
}

/* helper modified by LLM (iteration 2): arithmetic lemmas for bounds of the solution */
proof fn lemma_n_lt_d(y1: int, y2: int, y_w: int, x_b: int, y_b: int, r: int)
    requires
        valid_input(y1, y2, y_w, x_b, y_b, r),
    ensures
        2 <= compute_w(y_w, r) - y1 - r,
        compute_w(y_w, r) - y1 - r < compute_new_y1(y_w, r, y1, y_b),
{
    let w = compute_w(y_w, r);

    assert(y2 - y1 <= y_w - y1 - 1);
    assert(2 * r <= y_w - y1 - 2);

    let n = w - y1 - r;
    assert(n == y_w - r - y1 - r);
    assert(n == y_w - y1 - 2 * r);
    assert(2 <= n);

    assert(w - y_b == y_w - r - y_b);
    assert(w - y_b >= 1);

    let d = compute_new_y1(y_w, r, y1, y_b);
    assert(d == 2 * (y_w - r) - y1 - y_b - r);
    assert(d == (w - y1 - r) + (w - y_b));
    assert(n < d);
}

/* helper modified by LLM (iteration 2): generic division bound for positive denominator */
proof fn lemma_div_bound(a: int, b: int, c: int)
    requires
        a > 0,
        0 <= b,
        b < c,
        c > 0,
    ensures
        0 <= (a * b) / c,
        (a * b) / c < a,
{
    assert(0 <= a * b);
    assert(a * b < a * c);
    assert((a * b) / c < (a * c) / c);
    assert((a * c) / c == a);
}

/* helper modified by LLM (iteration 2): bounds for compute_solution used to justify i8 cast */
proof fn lemma_compute_solution_bounds(y1: int, y2: int, y_w: int, x_b: int, y_b: int, r: int)
    requires
        valid_input(y1, y2, y_w, x_b, y_b, r),
    ensures
        0 <= compute_solution(y1, y2, y_w, x_b, y_b, r),
        compute_solution(y1, y2, y_w, x_b, y_b, r) < x_b,
{
    let w = compute_w(y_w, r);
    let n = w - y1 - r;
    let d = compute_new_y1(y_w, r, y1, y_b);

    lemma_n_lt_d(y1, y2, y_w, x_b, y_b, r);
    assert(2 <= n);
    assert(n < d);
    assert(d > 0);

    let s = compute_solution(y1, y2, y_w, x_b, y_b, r);
    assert(s == x_b * n / d);

    lemma_div_bound(x_b, n, d);
    assert(0 <= x_b * n / d);
    assert(x_b * n / d < x_b);
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
    /* code modified by LLM (iteration 2): avoid direct `as int` casts in exec context by using spec i8-wrappers; prove cast safety in proof */
    if is_impossible_i8(y1, y2, y_w, x_b, y_b, r) {
        -1
    } else {
        proof {
            // Establish bounds to make the cast to i8 safe
            lemma_compute_solution_bounds(y1 as int, y2 as int, y_w as int, x_b as int, y_b as int, r as int);
            assert(0 <= compute_solution(y1 as int, y2 as int, y_w as int, x_b as int, y_b as int, r as int));
            assert(compute_solution(y1 as int, y2 as int, y_w as int, x_b as int, y_b as int, r as int) < x_b as int);
            assert(x_b as int <= 127);
            assert(-128 <= compute_solution(y1 as int, y2 as int, y_w as int, x_b as int, y_b as int, r as int));
            assert(compute_solution(y1 as int, y2 as int, y_w as int, x_b as int, y_b as int, r as int) <= 127);
        }
        let res: i8 = compute_solution_i8(y1, y2, y_w, x_b, y_b, r) as i8;
        res
    }
}
// </vc-code>


}

fn main() {}