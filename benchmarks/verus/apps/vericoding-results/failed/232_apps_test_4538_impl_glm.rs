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
/* helper modified by LLM (iteration 4): add helper to prevent arithmetic overflow */
spec fn safe_square(x: i8) -> int {
    (x as int) * (x as int)
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
/* code modified by LLM (iteration 5): replace int with Rust types in executable code */
{
    let d_sq: i32 = (d as i32) * (d as i32);
    let mut i: usize = 0;
    let mut count: i8 = 0;
    while i < n as usize
        invariant 
            0 <= count as int <= i as int,
            i as int <= n as int,
            count as int == count_points_within_distance(i as int, d as int, points@.map_values(|p: (i8, i8)| (p.0 as int, p.1 as int))),
        decreases (n as int) - (i as int)
    {
        let point = points[i];
        let x: i32 = point.0 as i32;
        let y: i32 = point.1 as i32;
        if x*x + y*y <= d_sq {
            count += 1;
        }
        i += 1;
    }
    count
}
// </vc-code>


}

fn main() {}