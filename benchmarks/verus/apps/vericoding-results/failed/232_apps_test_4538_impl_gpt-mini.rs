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
/* helper modified by LLM (iteration 5): relate Vec spec view to runtime indexing */
proof fn vec_map_index(points: Vec<(i8, i8)>, idx: int)
    requires
        0 <= idx,
        idx < points.len() as int,
    ensures
        points@.map_values(|p: (i8, i8)| (p.0 as int, p.1 as int))@[idx] == (points[idx as usize].0 as int, points[idx as usize].1 as int),
{
    proof {
        // the spec-level view of the Vec at index idx equals the runtime element at usize index
        assert(points@[idx] == points[idx as usize]);
        // mapping values on the spec-level sequence yields the cast pair
        assert(points@.map_values(|p: (i8, i8)| (p.0 as int, p.1 as int))@[idx] == (points@[idx].0 as int, points@[idx].1 as int));
        // combine to reach the desired equality relating spec mapping to runtime indexing
        assert((points@[idx].0 as int, points@[idx].1 as int) == (points[idx as usize].0 as int, points[idx as usize].1 as int));
    }
}

/* helper modified by LLM (iteration 5): relate filtered length when appending single element */
proof fn filter_len_append(seq: Seq<(int, int)>, k: int, d: int)
    requires
        0 <= k,
        k < seq.len() as int,
    ensures
        seq.subrange(0, k + 1).filter(|pt: (int, int)| within_distance(pt, d)).len() as int ==
        seq.subrange(0, k).filter(|pt: (int, int)| within_distance(pt, d)).len() as int +
        (if within_distance(seq@[k], d) { 1 } else { 0 }),
{
    proof {
        // split the extended prefix into prefix + singleton
        assert(seq.subrange(0, k + 1) == seq.subrange(0, k) + seq.subrange(k, k + 1));
        // the tail is a singleton containing seq@[k]
        assert(seq.subrange(k, k + 1).len() as int == 1);
        assert(seq.subrange(k, k + 1)@[0] == seq@[k]);
        // filtering distributes over concatenation
        assert(seq.subrange(0, k + 1).filter(|pt: (int, int)| within_distance(pt, d)) ==
               seq.subrange(0, k).filter(|pt: (int, int)| within_distance(pt, d)) + seq.subrange(k, k + 1).filter(|pt: (int, int)| within_distance(pt, d)));
        // the filtered singleton has length 1 iff its element satisfies the predicate
        assert(seq.subrange(k, k + 1).filter(|pt: (int, int)| within_distance(pt, d)).len() as int == (if within_distance(seq@[k], d) { 1 } else { 0 }));
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
/* code modified by LLM (iteration 5): iterate points using usize indices and maintain spec-level invariant with casts */
{
    let mut i: usize = 0;
    let mut cnt: i32 = 0;
    while i < n as usize
        invariant
            0 <= i as int,
            i as int <= n as int,
            0 <= cnt as int,
            cnt as int <= i as int,
            cnt as int == count_points_within_distance(i as int, d as int, points@.map_values(|p: (i8, i8)| (p.0 as int, p.1 as int))),
        decreases
            n as int - i as int
    {
        // compute squared distance using runtime integers
        let px = points[i].0 as i32;
        let py = points[i].1 as i32;
        let dd = d as i32;
        if px * px + py * py <= dd * dd {
            cnt = cnt + 1;
            proof {
                let seq = points@.map_values(|p: (i8, i8)| (p.0 as int, p.1 as int));
                vec_map_index(points, i as int);
                filter_len_append(seq, i as int, d as int);
                // after increment, the count equals the filtered length of the extended prefix
                assert(cnt as int == count_points_within_distance(i as int + 1, d as int, seq));
            }
        } else {
            proof {
                let seq = points@.map_values(|p: (i8, i8)| (p.0 as int, p.1 as int));
                vec_map_index(points, i as int);
                filter_len_append(seq, i as int, d as int);
                // without increment, the count still equals the filtered length of the extended prefix
                assert(cnt as int == count_points_within_distance(i as int + 1, d as int, seq));
            }
        }
        i = i + 1;
    }
    let result = cnt as i8;
    result
}

// </vc-code>


}

fn main() {}