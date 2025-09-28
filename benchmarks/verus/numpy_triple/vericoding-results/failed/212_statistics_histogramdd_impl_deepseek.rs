// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn find_bin(edge: Vec<i32>, value: i32) -> (bin: usize)
    requires
        edge.len() > 0,
        (forall|i: int| 0 <= i < edge.len() - 1 ==> edge[i] < edge[i + 1]),
        value >= edge[0],
    ensures
        bin <= edge.len() - 1,
        (bin == edge.len() - 1 ==> value >= edge[edge.len() - 1]),
        (bin < edge.len() - 1 ==> value >= edge@[bin] && value < edge@[bin + 1])
{
    let mut index: usize = 0;
    while index < edge.len() - 1
        invariant
            0 <= index <= edge.len() - 1,
            forall|i: int| 0 <= i <= index ==> edge@[i] <= value,
        decreases edge.len() - 1 - index
    {
        if value < edge@[index + 1] {
            break;
        } else {
            index = index + 1;
        }
    }
    index
}
/* helper modified by LLM (iteration 5): Fixed edge access using @ operator */
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
    /* code modified by LLM (iteration 5): Fixed edge access with @ operator */
    let mut edges_x: Vec<i32> = Vec::new();
    let mut edges_y: Vec<i32> = Vec::new();
    let mut hist: Vec<Vec<i32>> = Vec::with_capacity(bins_y);
    
    let mut current: i32 = 0;
    for i in 0..bins_x + 1 {
        edges_x.push(current);
        current = current + 1;
    }
    
    current = 0;
    for i in 0..bins_y + 1 {
        edges_y.push(current);
        current = current + 1;
    }
    
    for i in 0..bins_y {
        let mut row: Vec<i32> = Vec::with_capacity(bins_x);
        for j in 0..bins_x {
            row.push(0);
        }
        hist.push(row);
    }
    
    for point in sample {
        let (x, y) = point;
        let bin_x = find_bin(edges_x.clone(), x);
        let bin_y = find_bin(edges_y.clone(), y);
        
        if bin_x < bins_x && bin_y < bins_y {
            hist@[bin_y][bin_x] = hist@[bin_y][bin_x] + 1;
        }
    }
    
    (hist, edges_x, edges_y)
}
// </vc-code>

}
fn main() {}