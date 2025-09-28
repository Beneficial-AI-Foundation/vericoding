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
/* helper modified by LLM (iteration 5): fixed compilation error by using vstd::seq_lib::filter_push lemma */
proof fn count_points_incremental(i: int, d: int, points: Seq<(int, int)>)
    requires
        valid_input(i + 1, d, points),
    ensures
        count_points_within_distance(i + 1, d, points) ==
            count_points_within_distance(i, d, points) +
            (if within_distance(points[i], d) { 1 } else { 0 }),
{
    let f = |p: (int, int)| within_distance(p, d);
    let sub_i = points.subrange(0, i);
    let sub_i1 = points.subrange(0, i + 1);
    let p_i = points[i];

    assert(sub_i1 =~= sub_i.push(p_i));

    vstd::seq_lib::filter_push(sub_i, p_i, f);
    
    if f(p_i) {
        assert(sub_i1.filter(f).len() == sub_i.filter(f).len() + 1);
    } else {
        assert(sub_i1.filter(f).len() == sub_i.filter(f).len());
    }
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
/* code modified by LLM (iteration 5): code seems correct, updated comment */
{
    let mut i: i8 = 0;
    let mut count: i8 = 0;
    let ghost n_int = n as int;
    let ghost d_int = d as int;
    let ghost spec_points = points@.map_values(|p: (i8, i8)| (p.0 as int, p.1 as int));

    while i < n
        invariant
            0 <= i <= n,
            n_int == n as int,
            d_int == d as int,
            spec_points == points@.map_values(|p: (i8, i8)| (p.0 as int, p.1 as int)),
            valid_input(n_int, d_int, spec_points),
            0 <= count <= i,
            count as int == count_points_within_distance(i as int, d_int, spec_points),
        decreases n - i
    {
        let ghost i_int = i as int;
        proof {
            assert(i_int < n_int);
            assert(i_int + 1 <= n_int);
            assert(valid_input(i_int + 1, d_int, spec_points));
            count_points_incremental(i_int, d_int, spec_points);
        }

        assert(i_int < points@.len());
        let point = points[i as usize];
        
        let x = point.0 as i64;
        let y = point.1 as i64;
        let d_i64 = d as i64;
        
        proof {
            let p_int = spec_points[i_int];
            assert(x * x + y * y == (p_int.0 * p_int.0 + p_int.1 * p_int.1) as i64);
            assert(d_i64 * d_i64 == (d_int * d_int) as i64);
            assert((x * x + y * y <= d_i64 * d_i64) == within_distance(p_int, d_int));
        }

        if x * x + y * y <= d_i64 * d_i64 {
            count = count + 1;
        }

        i = i + 1;
    }

    count
}
// </vc-code>


}

fn main() {}