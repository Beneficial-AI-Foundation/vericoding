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
/* helper modified by LLM (iteration 5): No helper functions needed in this turn. */

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
/* code modified by LLM (iteration 5): Corrected type casting and moved calculations to ghost block. */
{
    let mut count: i8 = 0;
    let mut i: i8 = 0;
    let points_int_tuple = points@.map_values(|p: (i8, i8)| (p.0 as int, p.1 as int));

    while i < n
        invariant
            0 <= i as int,
            i as int <= n as int,
            0 <= count as int,
            count as int <= i as int,
            count as int == count_points_within_distance(i as int, d as int, points_int_tuple),
        decreases (n - i) as int
    {
        proof {
            assert((i as int) < (points.len() as int)) by (fences) ensures true;
            let p = points[i as usize];
            let ghost p_x_int = p.0 as int;
            let ghost p_y_int = p.1 as int;
            let ghost d_int = d as int;

            if p_x_int * p_x_int + p_y_int * p_y_int <= d_int * d_int {
                count = count + 1;
            }
        }

        i = i + 1;
    }
    count
}
// </vc-code>


}

fn main() {}