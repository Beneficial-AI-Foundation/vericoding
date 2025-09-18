// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): retained strictly_increasing predicate with explicit trigger */
spec fn strictly_increasing(s: Seq<i32>) -> bool {
    forall|i: int| 0 <= i && i + 1 < s.len() ==> #[trigger] s[i] < s[i + 1]
}
/* helper modified by LLM (iteration 5): retained nonnegativity predicate for 2D sequences with explicit triggers */
spec fn all_nonnegative_2d(m: Seq<Seq<i32>>) -> bool {
    forall|i: int, j: int| 0 <= i < m.len() && 0 <= j < m[i].len() ==> #[trigger] m[i][j] >= 0
}
// </vc-helpers>

// <vc-spec>
fn histogramdd(sample: Vec<(i32, i32)>, bins_x: usize, bins_y: usize) -> (result: (Vec<Vec<i32>>, Vec<i32>, Vec<i32>))
    requires 
        bins_x > 0,
        bins_y > 0,
    ensures 
        ({
            let (hist, edges_x, edges_y) = result;
            hist.len() == bins_y &&
            (forall|i: int| 0 <= i < hist.len() ==> #[trigger] hist[i].len() == bins_x) &&
            edges_x.len() == bins_x + 1 &&
            edges_y.len() == bins_y + 1 &&
            (forall|i: int| 0 <= i < bins_x ==> #[trigger] edges_x[i] < edges_x[i + 1]) &&
            (forall|i: int| 0 <= i < bins_y ==> #[trigger] edges_y[i] < edges_y[i + 1]) &&
            (forall|i: int, j: int| 0 <= i < bins_y && 0 <= j < bins_x ==> #[trigger] hist[i][j] >= 0) &&
            true
        })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use int counters for loops to avoid usize overflow and ensure decreases; maintain invariants; add truncation on casts for edges */
    let mut hist: Vec<Vec<i32>> = Vec::new();
    let mut y_i: int = 0;
    while y_i < bins_y as int
        invariant
            hist@.len() == y_i,
            0 <= y_i <= bins_y as int,
            forall|r: int| 0 <= r < hist@.len() ==> #[trigger] hist@[r].len() == bins_x as int,
            forall|r: int, c: int| 0 <= r < hist@.len() && 0 <= c < bins_x as int ==> #[trigger] hist@[r]@[c] >= 0
        decreases (bins_y as int) - y_i
    {
        let mut row: Vec<i32> = Vec::new();
        let mut x_i: int = 0;
        while x_i < bins_x as int
            invariant
                row@.len() == x_i,
                0 <= x_i <= bins_x as int,
                forall|c: int| 0 <= c < row@.len() ==> #[trigger] row@[c] >= 0
            decreases (bins_x as int) - x_i
        {
            row.push(0);
            x_i = x_i + 1;
        }
        proof {
            assert(row@.len() == bins_x as int);
            assert(forall|c: int| 0 <= c < bins_x as int ==> #[trigger] row@[c] >= 0);
        }
        hist.push(row);
        y_i = y_i + 1;
    }

    let mut edges_x: Vec<i32> = Vec::new();
    let mut ix_i: int = 0;
    while ix_i <= bins_x as int
        invariant
            edges_x@.len() == ix_i,
            0 <= ix_i <= bins_x as int + 1,
            forall|k: int| 0 <= k < edges_x@.len() ==> edges_x@[k] == k as i32
        decreases (bins_x as int) - ix_i + 1
    {
        let val_x: i32 = #[verifier::truncate] (ix_i as i32);
        edges_x.push(val_x);
        ix_i = ix_i + 1;
    }

    let mut edges_y: Vec<i32> = Vec::new();
    let mut iy_i: int = 0;
    while iy_i <= bins_y as int
        invariant
            edges_y@.len() == iy_i,
            0 <= iy_i <= bins_y as int + 1,
            forall|k: int| 0 <= k < edges_y@.len() ==> edges_y@[k] == k as i32
        decreases (bins_y as int) - iy_i + 1
    {
        let val_y: i32 = #[verifier::truncate] (iy_i as i32);
        edges_y.push(val_y);
        iy_i = iy_i + 1;
    }

    proof {
        assert(hist@.len() == bins_y as int);
        assert(forall|r: int| 0 <= r < hist@.len() ==> #[trigger] hist@[r].len() == bins_x as int);
        assert(edges_x@.len() == bins_x as int + 1);
        assert(edges_y@.len() == bins_y as int + 1);
        assert(forall|i: int| 0 <= i < bins_x as int ==> #[trigger] edges_x@[i] < edges_x@[i + 1]);
        assert(forall|i: int| 0 <= i < bins_y as int ==> #[trigger] edges_y@[i] < edges_y@[i + 1]);
        assert(forall|i: int, j: int| 0 <= i < hist@.len() && 0 <= j < bins_x as int ==> #[trigger] hist@[i]@[j] >= 0);
    }

    (hist, edges_x, edges_y)
}
// </vc-code>

}
fn main() {}