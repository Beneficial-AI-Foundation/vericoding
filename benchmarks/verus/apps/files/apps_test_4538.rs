// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
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
// </vc-helpers>

// <vc-spec>
fn solve(n: int, d: int, points: Seq<(int, int)>) -> (result: int)
    requires 
        valid_input(n, d, points),
    ensures 
        0 <= result <= n,
        result == count_points_within_distance(n, d, points)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}