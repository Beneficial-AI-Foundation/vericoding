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
/* helper modified by LLM (iteration 5): fixed overflow lemma to handle negative i8 values correctly */
proof fn lemma_no_overflow_i16(x: i8, y: i8, d: i8)
    ensures
        -32768 <= (x as i16) * (x as i16) <= 32767,
        -32768 <= (y as i16) * (y as i16) <= 32767,
        -32768 <= (d as i16) * (d as i16) <= 32767,
        -32768 <= (x as i16) * (x as i16) + (y as i16) * (y as i16) <= 32767,
{
    assert(-128 <= x <= 127);
    assert(-128 <= y <= 127);
    assert(-128 <= d <= 127);
    assert(0 <= (x as i16) * (x as i16) <= 128 * 128);
    assert(0 <= (y as i16) * (y as i16) <= 128 * 128);
    assert(0 <= (d as i16) * (d as i16) <= 128 * 128);
    assert(128 * 128 == 16384);
    assert((x as i16) * (x as i16) + (y as i16) * (y as i16) <= 16384 + 16384);
    assert(16384 + 16384 == 32768);
    assert(32768 <= 32767 + 1);
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
    /* code modified by LLM (iteration 5): fixed loop invariant and assertions */
    let mut count: i8 = 0;
    let mut i: usize = 0;
    
    while i < n as usize
        invariant
            0 <= i <= n as int,
            0 <= count as int <= i,
            count as int == points@.subrange(0, i as int).map_values(|p: (i8, i8)| (p.0 as int, p.1 as int)).filter(|point: (int, int)| within_distance(point, d as int)).len(),
            valid_input(n as int, d as int, points@.map_values(|p: (i8, i8)| (p.0 as int, p.1 as int))),
        decreases n as int - i as int
    {
        let x = points[i].0;
        let y = points[i].1;
        
        // Use i16 to avoid overflow when squaring i8 values
        let x_16: i16 = x as i16;
        let y_16: i16 = y as i16;
        let d_16: i16 = d as i16;
        
        proof {
            lemma_no_overflow_i16(x, y, d);
        }
        
        let old_count = count;
        let old_i = i;
        
        if x_16 * x_16 + y_16 * y_16 <= d_16 * d_16 {
            count = count + 1;
            proof {
                assert(within_distance((x as int, y as int), d as int));
                assert(points@[i as int] == (x, y));
                let filtered_old = points@.subrange(0, i as int).map_values(|p: (i8, i8)| (p.0 as int, p.1 as int)).filter(|point: (int, int)| within_distance(point, d as int));
                let filtered_new = points@.subrange(0, (i + 1) as int).map_values(|p: (i8, i8)| (p.0 as int, p.1 as int)).filter(|point: (int, int)| within_distance(point, d as int));
                assert(filtered_new.len() == filtered_old.len() + 1);
            }
        } else {
            proof {
                assert(!within_distance((x as int, y as int), d as int));
                let filtered_old = points@.subrange(0, i as int).map_values(|p: (i8, i8)| (p.0 as int, p.1 as int)).filter(|point: (int, int)| within_distance(point, d as int));
                let filtered_new = points@.subrange(0, (i + 1) as int).map_values(|p: (i8, i8)| (p.0 as int, p.1 as int)).filter(|point: (int, int)| within_distance(point, d as int));
                assert(filtered_new.len() == filtered_old.len());
            }
        }
        
        i = i + 1;
        
        proof {
            assert(count as int == points@.subrange(0, i as int).map_values(|p: (i8, i8)| (p.0 as int, p.1 as int)).filter(|point: (int, int)| within_distance(point, d as int)).len());
        }
    }
    
    proof {
        assert(i == n as int);
        assert(points@.subrange(0, n as int) =~= points@.subrange(0, n as int));
        assert(count as int == count_points_within_distance(n as int, d as int, points@.map_values(|p: (i8, i8)| (p.0 as int, p.1 as int))));
    }
    
    count
}
// </vc-code>


}

fn main() {}