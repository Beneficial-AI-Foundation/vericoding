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
proof fn lemma_subrange_push<T>(s: Seq<T>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.subrange(0, i + 1) == s.subrange(0, i).push(s[i]),
{
}

proof fn lemma_filter_len_push_within_distance(s: Seq<(int, int)>, d: int, x: (int, int))
    ensures
        (s.push(x)).filter(|p: (int, int)| within_distance(p, d)).len()
        ==
        s.filter(|p: (int, int)| within_distance(p, d)).len()
        + (if within_distance(x, d) { 1 } else { 0 }),
{
}

proof fn lemma_map_index_points(points: Seq<(i8, i8)>, i: int)
    requires
        0 <= i < points.len(),
    ensures
        (points.map_values(|p: (i8, i8)| (p.0 as int, p.1 as int)))[i]
        ==
        (points[i].0 as int, points[i].1 as int),
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
    let n_int: int = n as int;
    let d_int: int = d as int;
    let mps: Seq<(int, int)> = points@.map_values(|p: (i8, i8)| (p.0 as int, p.1 as int));
    let mut i: int = 0;
    let mut count: i8 = 0i8;
    while i < n_int
        invariant
            0 <= i <= n_int,
            0 <= count as int <= i,
            points.len() as int >= n_int,
            mps == points@.map_values(|p: (i8, i8)| (p.0 as int, p.1 as int)),
            count as int == mps.subrange(0, i).filter(|q: (int, int)| within_distance(q, d_int)).len() as int,
        decreases n_int - i
    {
        assert(i < points.len() as int);
        let p = points[i as usize];
        let xi: int = p.0 as int;
        let yi: int = p.1 as int;
        let cond: bool = xi * xi + yi * yi <= d_int * d_int;
        proof {
            lemma_map_index_points(points@, i);
            assert(points@[i] == p);
            assert((xi, yi) == (points@[i].0 as int, points@[i].1 as int));
            assert(cond == within_distance((xi, yi), d_int));
            assert(mps[i] == (xi, yi));
        }
        if cond {
            proof {
                assert(count as int <= i);
                assert(i < n_int);
                // Since i < n_int and count <= i, we have (count as int) + 1 <= n_int,
                // and as n is i8, n_int <= 127, so no overflow on i8 increment.
            }
            count = count + 1i8;
        }
        proof {
            // Establish the invariant for the next iteration (i -> i + 1)
            lemma_subrange_push::<(int, int)>(mps, i);
            lemma_filter_len_push_within_distance(mps.subrange(0, i), d_int, mps[i]);
            assert(
                (mps.subrange(0, i + 1).filter(|q: (int, int)| within_distance(q, d_int)).len() as int)
                ==
                (mps.subrange(0, i).filter(|q: (int, int)| within_distance(q, d_int)).len() as int)
                + (if cond { 1 } else { 0 })
            );
        }
        i = i + 1;
        proof {
            assert(count as int == mps.subrange(0, i).filter(|q: (int, int)| within_distance(q, d_int)).len() as int);
        }
    }
    assert(count as int == count_points_within_distance(n_int, d_int, mps));
    count
}
// </vc-code>


}

fn main() {}