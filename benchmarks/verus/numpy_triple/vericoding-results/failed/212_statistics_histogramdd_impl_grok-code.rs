// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fixed compilation by avoiding mutable indexing using immutable Map for counting, clamped indices to handle i32 to usize conversion safely */
    let mut hist = Vec::<Vec<i32>>::new();
    let mut edges_x = Vec::<i32>::new();
    let mut edges_y = Vec::<i32>::new();
    for i in 0..(bins_x + 1) {
        edges_x.push(#[verifier::truncate] (i as i32));
    }
    for i in 0..(bins_y + 1) {
        edges_y.push(#[verifier::truncate] (i as i32));
    }
    let mut counter = vstd::map::Map::<(usize, usize), i32>::empty();
    for (sx, sy) in sample.iter() {
        let x_index = if *sx < 0 {
            0
        } else if *sx >= (bins_x as i32) {
            bins_x - 1
        } else {
            (*sx as usize)
        };
        let y_index = if *sy < 0 {
            0
        } else if *sy >= (bins_y as i32) {
            bins_y - 1
        } else {
            (*sy as usize)
        };
        let key = (y_index, x_index);
        let count = counter.get(key).unwrap_or(0);
        counter = counter.insert(key, count + 1);
    }
    for yi in 0..bins_y {
        let mut row = Vec::new();
        for xi in 0..bins_x {
            let count = counter.get(&(yi, xi)).unwrap_or(0);
            row.push(count);
        }
        hist.push(row);
    }
    proof {
        assert(hist@.len() == bins_y);
        assert(forall|i: int| 0 <= i < hist@.len() ==> hist@[i].len() == bins_x);
        assert(edges_x@.len() == bins_x + 1);
        assert(edges_y@.len() == bins_y + 1);
        assert(forall|i: int| 0 <= i < bins_x ==> edges_x@[i] == (i as i32) && edges_x@[i] < edges_x@[i + 1]);
        assert(forall|i: int| 0 <= i < bins_y ==> edges_y@[i] == (i as i32) && edges_y@[i] < edges_y@[i + 1]);
        assert(forall|i: int, j: int| 0 <= i < hist@.len() && 0 <= j < hist@[i].len() ==> hist@[i][j] >= 0);
        assert(forall|yi: usize, xi: usize| yi < bins_y && xi < bins_x ==> hist@[yi as int][xi as int] == counter.get(&(yi, xi)).unwrap_or(0));
    }
    (hist, edges_x, edges_y)
}
// </vc-code>

}
fn main() {}