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
/* code modified by LLM (iteration 5): Fixed arithmetic overflow by using i32 types for distances and changed count to usize to avoid potential overflow */
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < n as usize
        invariant
            points@.len() >= n as int,
            0 <= i as int <= n as int,
            count == count_points_within_distance(i as int, d as int, points@.map_values(|p: (i8, i8)| (p.0 as int, p.1 as int))), 
        decreases n as int - i as int
    {
        let p = points[i];
        let x = p.0 as i32;
        let y = p.1 as i32;
        let dist_sq = x * x + y * y;
        let d_sq = (d as i32) * (d as i32);
        if dist_sq <= d_sq {
            count = count + 1;
        }
        i = i + 1;
    }
    count as i8
}
// </vc-code>


}

fn main() {}