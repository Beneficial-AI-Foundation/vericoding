// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// No helper functions needed for this implementation
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
    /* code modified by LLM (iteration 5): fixed compilation error by changing vstd::vec_lib to vstd::vec */
    let mut edges_x = Vec::new();
    let mut i_x: usize = 0;
    while i_x <= bins_x
        invariant
            i_x <= bins_x + 1,
            edges_x.len() == i_x,
            forall|j: int| 0 <= j < i_x ==> edges_x[j] as int == j,
    {
        edges_x.push(i_x as i32);
        i_x += 1;
    }

    let mut edges_y = Vec::new();
    let mut i_y: usize = 0;
    while i_y <= bins_y
        invariant
            i_y <= bins_y + 1,
            edges_y.len() == i_y,
            forall|j: int| 0 <= j < i_y ==> edges_y[j] as int == j,
    {
        edges_y.push(i_y as i32);
        i_y += 1;
    }

    let mut hist = Vec::new();
    let mut i: usize = 0;
    while i < bins_y
        invariant
            i <= bins_y,
            hist.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] hist[j].len() == bins_x,
            forall|j: int, k: int| 0 <= j < i && 0 <= k < bins_x ==> #[trigger] hist[j][k] == 0,
    {
        let row = vec![0i32; bins_x];
        proof {
            vstd::vec::vec_new_const_lemma::<i32>(bins_x, 0i32);
        }
        hist.push(row);
        i += 1;
    }

    let mut s_idx: usize = 0;
    while s_idx < sample.len()
        invariant
            s_idx <= sample.len(),
            hist.len() == bins_y,
            forall|i: int| 0 <= i < hist.len() ==> #[trigger] hist[i].len() == bins_x,
            forall|i: int, j: int| 0 <= i < bins_y && 0 <= j < bins_x ==> #[trigger] hist[i][j] >= 0,
    {
        let p = sample[s_idx];
        let px = p.0;
        let py = p.1;

        if 0 <= px && (px as usize) < bins_x && 0 <= py && (py as usize) < bins_y {
            let bin_x = px as usize;
            let bin_y = py as usize;
            hist[bin_y].set(bin_x, hist[bin_y][bin_x] + 1);
        }
        s_idx += 1;
    }

    (hist, edges_x, edges_y)
}
// </vc-code>

}
fn main() {}