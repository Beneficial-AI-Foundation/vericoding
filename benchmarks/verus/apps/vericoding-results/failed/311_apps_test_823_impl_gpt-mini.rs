// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(x: int, y: int) -> bool {
    -100 <= x <= 100 && -100 <= y <= 100
}

spec fn is_origin_or_first_point(x: int, y: int) -> bool {
    (x == 0 && y == 0) || (x == 1 && y == 0)
}

spec fn is_right_edge(x: int, y: int) -> bool {
    x >= 1 && -x + 1 < y <= x
}

spec fn is_left_edge(x: int, y: int) -> bool {
    x < 0 && x <= y < -x
}

spec fn is_top_edge(x: int, y: int) -> bool {
    y > 0 && -y <= x < y
}

spec fn compute_turns(x: int, y: int) -> int
    recommends valid_input(x, y)
{
    if is_origin_or_first_point(x, y) { 
        0
    } else if is_right_edge(x, y) { 
        1 + 4 * (x - 1)
    } else if is_left_edge(x, y) { 
        3 + 4 * (-x - 1)
    } else if is_top_edge(x, y) { 
        2 + 4 * (y - 1)
    } else { 
        -4 * y
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate spec compute_turns to its branch expression */
proof fn compute_turns_equiv(x: int, y: int)
    requires
        valid_input(x, y),
    ensures
        compute_turns(x, y) == if is_origin_or_first_point(x, y) { 0::<int> } else if is_right_edge(x, y) { 1::<int> + 4::<int> * (x - 1::<int>) } else if is_left_edge(x, y) { 3::<int> + 4::<int> * (-x - 1::<int>) } else if is_top_edge(x, y) { 2::<int> + 4::<int> * (y - 1::<int>) } else { (-4::<int>) * y },
    decreases
        0::<nat>,
{
    proof {
        reveal(compute_turns);
        assert(compute_turns(x, y) == if is_origin_or_first_point(x, y) { 0::<int> } else if is_right_edge(x, y) { 1::<int> + 4::<int> * (x - 1::<int>) } else if is_left_edge(x, y) { 3::<int> + 4::<int> * (-x - 1::<int>) } else if is_top_edge(x, y) { 2::<int> + 4::<int> * (y - 1::<int>) } else { (-4::<int>) * y });
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(x: i8, y: i8) -> (result: i8)
    requires 
        valid_input(x as int, y as int)
    ensures 
        result as int >= 0,
        result as int == compute_turns(x as int, y as int),
        is_origin_or_first_point(x as int, y as int) ==> result as int == 0,
        is_right_edge(x as int, y as int) ==> result as int == 1 + 4 * (x as int - 1),
        is_left_edge(x as int, y as int) ==> result as int == 3 + 4 * (-(x as int) - 1),
        is_top_edge(x as int, y as int) ==> result as int == 2 + 4 * (y as int - 1),
        !(is_origin_or_first_point(x as int, y as int) || is_right_edge(x as int, y as int) || is_left_edge(x as int, y as int) || is_top_edge(x as int, y as int)) ==> result as int == -4 * y as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute runtime equivalent of compute_turns without using spec ints */
    let tx: i32 = x as i32;
    let ty: i32 = y as i32;
    let t_i32: i32;
    if tx == 0 && ty == 0 {
        t_i32 = 0;
    } else if tx >= 1 && (-tx + 1) < ty && ty <= tx {
        t_i32 = 1 + 4 * (tx - 1);
    } else if tx < 0 && tx <= ty && ty < -tx {
        t_i32 = 3 + 4 * ((-tx) - 1);
    } else if ty > 0 && (-ty) <= tx && tx < ty {
        t_i32 = 2 + 4 * (ty - 1);
    } else {
        t_i32 = -4 * ty;
    }
    let result = t_i32 as i8;
    proof {
        let xi: int = x as int;
        let yi: int = y as int;
        let gt: int = t_i32 as int;
        compute_turns_equiv(xi, yi);
        if is_origin_or_first_point(xi, yi) {
            assert(xi == 0 && yi == 0);
            assert(tx as int == xi);
            assert(ty as int == yi);
            assert(gt == 0::<int>);
        } else if is_right_edge(xi, yi) {
            assert(tx as int == xi);
            assert(ty as int == yi);
            assert(xi >= 1 && (-xi + 1) < yi && yi <= xi);
            assert(tx >= 1 && (-tx + 1) < ty && ty <= tx);
            assert(gt == 1::<int> + 4::<int> * (xi - 1::<int>));
        } else if is_left_edge(xi, yi) {
            assert(tx as int == xi);
            assert(ty as int == yi);
            assert(xi < 0 && xi <= yi && yi < -xi);
            assert(tx < 0 && tx <= ty && ty < -tx);
            assert(gt == 3::<int> + 4::<int> * (-xi - 1::<int>));
        } else if is_top_edge(xi, yi) {
            assert(tx as int == xi);
            assert(ty as int == yi);
            assert(yi > 0 && (-yi) <= xi && xi < yi);
            assert(ty > 0 && (-ty) <= tx && tx < ty);
            assert(gt == 2::<int> + 4::<int> * (yi - 1::<int>));
        } else {
            assert(gt == (-4::<int>) * yi);
        }
        assert(result as int == compute_turns(xi, yi));
    }
    result
}

// </vc-code>


}

fn main() {}