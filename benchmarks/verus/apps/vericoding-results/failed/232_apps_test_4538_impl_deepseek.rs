// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, d: int, points: Seq<(int, int)>) -> bool {
    n >= 0 && d >= 0 && points.len() >= n
}

spec fn within_distance(point: (int, int), d: int) -> bool {
    point.0 * point.0 + point.1 * point.1 <= d * d
}

spec fn count_points_within_distance(n: int, d: int, points: Seq<(int, int)>) -> int
    recommends valid_input(n, d, points)
{
    points.subrange(0, n).filter(|point: (int, int)| within_distance(point, d)).len() as int
}
// </vc-preamble>

// <vc-helpers>

proof fn lemma_sq_nonnegative(x: int) 
    ensures
        x * x >= 0,
{
    if x >= 0 {
        assert(x * x >= 0);
    } else {
        assert(x * x >= 0);
    }
}

proof fn lemma_square_cmp(a: int, b: int)
    requires
        a >= 0 && b >= 0,
    ensures
        a * a <= b * b ==> a <= b,
        a <= b ==> a * a <= b * b,
{
    if a <= b {
        assert(forall|x: int, y: int| x <= y && x >= 0 && y >= 0 ==> x * x <= y * y);
    } else {
        assert(forall|x: int, y: int| x > y && x >= 0 && y >= 0 ==> x * x > y * y);
    }
}

spec fn i8_sq_positive(x: i8) -> bool {
    x >= 0
}

/* helper modified by LLM (iteration 5): Removed ghost assignment syntax */
spec fn squared_norm(point: (i8, i8)) -> int {
    (point.0 as int) * (point.0 as int) + (point.1 as int) * (point.1 as int)
}

spec fn d_squared_spec(d: i8) -> int {
    (d as int) * (d as int)
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, d: i8, points: Vec<(i8, i8)>) -> (result: i8)
    requires 
        valid_input(n as int, d as int, points@.map_values(|p: (i8, i8)| (p.0 as int, p.1 as int))),
    ensures 
        0 <= result as int <= n as int,
        result as int == count_points_within_distance(n as int, d as int, points@.map_values(|p: (i8, i8)| (p.0 as int, p.1 as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed ghost variable syntax error */
    let mut count: i8 = 0;
    let mut i: usize = 0;
    
    while i < (n as usize)
        invariant
            i <= n as usize,
            count as int == count_points_within_distance(i as int, d as int, points@.subrange(0, i as int).map_values(|p: (i8, i8)| (p.0 as int, p.1 as int))),
    {
        let point = points[i];
        let x_sq = (point.0 as int) * (point.0 as int);
        let y_sq = (point.1 as int) * (point.1 as int);
        let d_sq = (d as int) * (d as int);
        
        if x_sq + y_sq <= d_sq {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}