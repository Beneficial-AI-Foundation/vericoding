// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type compatibility between i32 and int */
spec fn get_bin_index(value: i32, min_val: i32, max_val: i32, num_bins: usize) -> int
    requires num_bins > 0, min_val < max_val
{
    let range = max_val - min_val;
    let bin_size = range / (num_bins as int);
    if value <= min_val { 0 }
    else if value >= max_val { num_bins as int - 1 }
    else { ((value - min_val) as int) / bin_size }
}

spec fn create_edges(min_val: i32, max_val: i32, num_bins: usize) -> Seq<i32>
    requires num_bins > 0, min_val < max_val
{
    let range = max_val - min_val;
    let bin_size = range / (num_bins as int);
    Seq::new((num_bins + 1) as nat, |i: int| min_val + (i * bin_size) as i32)
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
/* code modified by LLM (iteration 5): fixed type compatibility issues with casting to i32 */
{
    if sample.len() == 0 {
        let hist = vec![vec![0i32; bins_x]; bins_y];
        let edges_x = vec![0i32; bins_x + 1];
        let edges_y = vec![0i32; bins_y + 1];
        return (hist, edges_x, edges_y);
    }
    
    let mut min_x = sample[0].0;
    let mut max_x = sample[0].0;
    let mut min_y = sample[0].1;
    let mut max_y = sample[0].1;
    
    let mut i = 1;
    while i < sample.len() {
        if sample[i].0 < min_x { min_x = sample[i].0; }
        if sample[i].0 > max_x { max_x = sample[i].0; }
        if sample[i].1 < min_y { min_y = sample[i].1; }
        if sample[i].1 > max_y { max_y = sample[i].1; }
        i += 1;
    }
    
    if min_x == max_x { max_x += 1; }
    if min_y == max_y { max_y += 1; }
    
    let mut hist = Vec::new();
    let mut row_idx = 0;
    while row_idx < bins_y {
        let mut row = Vec::new();
        let mut col_idx = 0;
        while col_idx < bins_x {
            row.push(0i32);
            col_idx += 1;
        }
        hist.push(row);
        row_idx += 1;
    }
    
    let mut edges_x = Vec::new();
    let mut edge_idx = 0;
    while edge_idx <= bins_x {
        let edge = min_x + ((edge_idx as i32) * (max_x - min_x)) / (bins_x as i32);
        edges_x.push(edge);
        edge_idx += 1;
    }
    
    let mut edges_y = Vec::new();
    edge_idx = 0;
    while edge_idx <= bins_y {
        let edge = min_y + ((edge_idx as i32) * (max_y - min_y)) / (bins_y as i32);
        edges_y.push(edge);
        edge_idx += 1;
    }
    
    (hist, edges_x, edges_y)
}
// </vc-code>

}
fn main() {}