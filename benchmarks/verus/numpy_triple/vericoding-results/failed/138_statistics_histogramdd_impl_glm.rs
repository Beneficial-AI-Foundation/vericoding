// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed indexing issue by using set method */
fn compute_histogram_and_edges(sample: Vec<(i32, i32)>, bins_x: usize, bins_y: usize) -> (result: (Vec<Vec<i32>>, Vec<i32>, Vec<i32>))
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
{
    // Find min and max for x coordinates
    let mut min_x = if sample.len() > 0 { sample[0].0 } else { 0 };
    let mut max_x = if sample.len() > 0 { sample[0].0 } else { 0 };
    let mut min_y = if sample.len() > 0 { sample[0].1 } else { 0 };
    let mut max_y = if sample.len() > 0 { sample[0].1 } else { 0 };
    
    for i in 0..sample.len() {
        if sample[i].0 < min_x {
            min_x = sample[i].0;
        }
        if sample[i].0 > max_x {
            max_x = sample[i].0;
        }
        if sample[i].1 < min_y {
            min_y = sample[i].1;
        }
        if sample[i].1 > max_y {
            max_y = sample[i].1;
        }
    }
    
    // Compute bin edges
    let x_step = ((max_x - min_x + 1) / bins_x as i32).max(1);
    let y_step = ((max_y - min_y + 1) / bins_y as i32).max(1);
    
    let mut edges_x = vec![0i32; bins_x + 1];
    let mut edges_y = vec![0i32; bins_y + 1];
    
    for i in 0..bins_x + 1 {
        edges_x[i] = min_x + i as i32 * x_step;
    }
    
    for i in 0..bins_y + 1 {
        edges_y[i] = min_y + i as i32 * y_step;
    }
    
    // Initialize flat histogram vector
    let mut hist_flat = vec![0i32; bins_x * bins_y];
    
    // Compute histogram
    for i in 0..sample.len() {
        let x_coord = sample[i].0;
        let y_coord = sample[i].1;
        
        // Clamp the bin indices to [0, bins_x-1] and [0, bins_y-1]
        let x_idx = ((x_coord - min_x) / x_step).min((bins_x - 1) as i32).max(0) as usize;
        let y_idx = ((y_coord - min_y) / y_step).min((bins_y - 1) as i32).max(0) as usize;
        
        let flat_idx = y_idx * bins_x + x_idx;
        // We know flat_idx is in bounds because x_idx in [0, bins_x-1] and y_idx in [0, bins_y-1]
        let current = hist_flat[flat_idx];
        hist_flat.set(flat_idx, current + 1);
    }
    
    // Convert flat histogram to 2D
    let mut hist = Vec::new();
    for i in 0..bins_y {
        let mut row = Vec::new();
        for j in 0..bins_x {
            let flat_idx = i * bins_x + j;
            row.push(hist_flat[flat_idx]);
        }
        hist.push(row);
    }
    
    (hist, edges_x, edges_y)
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
/* code modified by LLM (iteration 4): no changes as error was in helper */
{
    compute_histogram_and_edges(sample, bins_x, bins_y)
}
// </vc-code>

}
fn main() {}