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
/* helper modified by LLM (iteration 5): changed function mode to proof */
proof fn lemma_count_points_bounds(n: int, d: int, points: Seq<(int, int)>)
    requires valid_input(n, d, points)
    ensures 0 <= count_points_within_distance(n, d, points) <= n
{
}

proof fn lemma_count_points_empty(d: int, points: Seq<(int, int)>)
    requires valid_input(0, d, points)
    ensures count_points_within_distance(0, d, points) == 0
{
}

proof fn lemma_count_points_step(n: int, d: int, points: Seq<(int, int)>)
    requires
        valid_input(n + 1, d, points),
        n >= 0
    ensures
        count_points_within_distance(n + 1, d, points) == 
        count_points_within_distance(n, d, points) + 
        (if within_distance(points[n], d) { 1int } else { 0int })
{
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
    /* code modified by LLM (iteration 5): added decreases clause to while loop */
    let mut count: i8 = 0;
    let mut i: i8 = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            0 <= count <= i,
            count as int == count_points_within_distance(i as int, d as int, points@.map_values(|p: (i8, i8)| (p.0 as int, p.1 as int)))
        decreases n - i
    {
        proof {
            lemma_count_points_step(i as int, d as int, points@.map_values(|p: (i8, i8)| (p.0 as int, p.1 as int)));
        }
        
        let point = points[i as usize];
        let x = point.0;
        let y = point.1;
        
        if x * x + y * y <= d * d {
            count = count + 1;
        }
        
        i = i + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}