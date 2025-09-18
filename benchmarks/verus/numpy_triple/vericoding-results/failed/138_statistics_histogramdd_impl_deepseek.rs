// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed syntax by adding proper braces to proof function bodies and proper while loop invariants */
    proof fn find_bin_x(edge: int, edges: Seq<int>, bins: int) -> (bin: usize)
        requires
            bins > 0,
            edges.len() == bins + 1,
            forall|i: int| 0 <= i < bins ==> #[trigger] edges[i] < edges[i + 1]
        ensures
            0 <= bin < bins || bin == bins,
            bin == bins ==> edge > edges[bins],
            bin < bins ==> edges[bin] <= edge < edges[bin + 1]
    {
        if edge < edges[0] {
            0
        } else if edge >= edges[bins] {
            bins
        } else {
            let mut bin_idx: int = 0;
            assert(0 <= bin_idx < bins);
            assert(edge >= edges[bin_idx]);
            while bin_idx < bins - 1 && edge >= edges[bin_idx + 1]
                invariant
                    0 <= bin_idx < bins,
                    edge >= edges[bin_idx]
            {
                bin_idx = bin_idx + 1;
            }
            bin_idx as usize
        }
    }

    proof fn find_bin_y(edge: int, edges: Seq<int>, bins: int) -> (bin: usize)
        requires
            bins > 0,
            edges.len() == bins + 1,
            forall|i: int| 0 <= i < bins ==> #[trigger] edges[i] < edges[i + 1]
        ensures
            0 <= bin < bins || bin == bins,
            bin == bins ==> edge > edges[bins],
            bin < bins ==> edges[bin] <= edge < edges[bin + 1]
    {
        if edge < edges[0] {
            0
        } else if edge >= edges[bins] {
            bins
        } else {
            let mut bin_idx: int = 0;
            assert(0 <= bin_idx < bins);
            assert(edge >= edges[bin_idx]);
            while bin_idx < bins - 1 && edge >= edges[bin_idx + 1]
                invariant
                    0 <= bin_idx < bins,
                    edge >= edges[bin_idx]
            {
                bin_idx = bin_idx + 1;
            }
            bin_idx as usize
        }
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
/* code modified by LLM (iteration 5): Fixed loop invariant syntax by adding curly braces */
{
    let mut hist = Vec::<Vec<i32>>::with_capacity(bins_y);
    let mut edges_x = Vec::<i32>::new();
    let mut edges_y = Vec::<i32>::new();
    
    // Initialize histogram with zeros
    let mut i = 0;
    while i < bins_y
        invariant 0 <= i <= bins_y,
        invariant hist.len() == i,
        invariant forall|j: int| 0 <= j < i ==> #[trigger] hist[j].len() == bins_x,
        invariant forall|j: int, k: int| 0 <= j < i && 0 <= k < bins_x ==> #[trigger] hist[j][k] == 0
    {
        let mut row = Vec::<i32>::with_capacity(bins_x);
        let mut j = 0;
        while j < bins_x
            invariant 0 <= j <= bins_x,
            invariant row.len() == j,
            invariant forall|k: int| 0 <= k < j ==> #[trigger] row[k] == 0
        {
            row.push(0);
            j += 1;
        }
        hist.push(row);
        i += 1;
    }
    
    // Process each sample point
    let mut idx = 0;
    while idx < sample.len()
        invariant 0 <= idx <= sample.len()
    {
        let (x, y) = sample[idx];
        
        // Find bin for x coordinate
        let ghost_bins_x = bins_x as int;
        let ghost_bins_y = bins_y as int;
        proof {
            let bin_x = find_bin_x(x, edges_x@, ghost_bins_x);
            let bin_y = find_bin_y(y, edges_y@, ghost_bins_y);
        }
        
        idx += 1;
    }
    
    (hist, edges_x, edges_y)
}
// </vc-code>

}
fn main() {}