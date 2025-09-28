// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: int, b: int) -> bool {
    n > 0 && a > 0 && b > 0
}

spec fn valid_output(result: Seq<int>, n: int, a: int, b: int) -> bool {
    result.len() == 3 &&
    result[0] >= 6 * n &&
    result[1] > 0 && result[2] > 0 &&
    result[0] == result[1] * result[2] &&
    ((result[1] >= a && result[2] >= b) || (result[1] >= b && result[2] >= a))
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_factor_exists(target: i8, a: i8, b: i8, min_dim: i8)
    requires target > 0, a > 0, b > 0, min_dim > 0
    ensures exists|w: i8, h: i8| #[trigger] (w * h) >= target && w >= min_dim && h >= min_dim && 
            ((w >= a && h >= b) || (w >= b && h >= a))
{
    let max_ab = if a > b { a } else { b };
    let min_required = if target % max_ab == 0 { target / max_ab } else { target / max_ab + 1 };
    let other_dim = if min_required > max_ab { min_required } else { max_ab };
    let this_dim = max_ab;
    
    assert(#[trigger] (this_dim * other_dim) >= target);
    assert(this_dim >= min_dim);
    assert(other_dim >= min_dim);
    assert((this_dim >= a && other_dim >= b) || (this_dim >= b && other_dim >= a));
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8) -> (result: Vec<i8>)
    requires valid_input(n as int, a as int, b as int)
    ensures valid_output(result@.map(|i, x| x as int), n as int, a as int, b as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use lemma to find valid dimensions */
    let target_area = 6 * n;
    let min_dim = if a > b { a } else { b };
    
    proof {
        lemma_factor_exists(target_area, a, b, min_dim);
    }
    
    let mut width = min_dim;
    let mut height = min_dim;
    
    while width * height < target_area
        invariant width >= min_dim, height >= min_dim
        decreases (target_area - width * height) as nat
    {
        if width <= height {
            width += 1;
        } else {
            height += 1;
        }
    }
    
    let area = width * height;
    let result = vec![area, width, height];
    result
}
// </vc-code>


}

fn main() {}