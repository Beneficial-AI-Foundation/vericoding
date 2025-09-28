// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added type annotations to fix compilation errors */
spec fn valid_histogram(hist: Vec<Vec<i32>>, bins_x: usize, bins_y: usize) -> bool {
    hist.len() == bins_y &&
    (forall|i: int| 0 <= i < hist.len() ==> #[trigger] hist[i].len() == bins_x) &&
    (forall|i: int, j: int| 0 <= i < bins_y && 0 <= j < bins_x ==> #[trigger] hist[i][j] >= 0)
}

spec fn valid_edges(edges: Vec<i32>, bins: usize) -> bool {
    edges.len() == bins + 1 &&
    (forall|i: int| 0 <= i < bins ==> #[trigger] edges[i] < edges[i + 1])
}

fn create_edges(min_val: i32, max_val: i32, bins: usize) -> (edges: Vec<i32>)
    requires
        bins > 0,
        min_val <= max_val,
    ensures
        edges.len() == bins + 1,
        edges[0] == min_val,
        edges[bins as int] == max_val + 1,
        (forall|i: int| 0 <= i < bins ==> #[trigger] edges[i] < edges[i + 1]),
{
    let mut edges: Vec<i32> = Vec::new();
    let range = (max_val - min_val + 1) as usize;
    let bin_size = if range % bins == 0 { range / bins } else { range / bins + 1 };
    
    let mut i: usize = 0;
    while i <= bins
        invariant
            edges.len() == i,
            i <= bins + 1,
            (forall|j: int| 0 <= j < i - 1 ==> #[trigger] edges[j] < edges[j + 1]),
            i > 0 ==> edges[0] == min_val,
    {
        if i == 0 {
            edges.push(min_val);
        } else if i == bins {
            edges.push(max_val + 1);
        } else {
            let next_edge = min_val + (i * bin_size) as i32;
            edges.push(next_edge);
        }
        i = i + 1;
    }
    edges
}

fn find_bin(value: i32, edges: Vec<i32>) -> (bin: usize)
    requires
        edges.len() > 1,
        (forall|i: int| 0 <= i < edges.len() - 1 ==> #[trigger] edges[i] < edges[i + 1]),
    ensures
        bin < edges.len() - 1,
{
    let mut i: usize = 0;
    while i < edges.len() - 2
        invariant
            i < edges.len() - 1,
    {
        if value < edges[i + 1] {
            return i;
        }
        i = i + 1;
    }
    edges.len() - 2
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
    /* code modified by LLM (iteration 3): Added type annotations for Vec::new() to fix compilation */
    if sample.len() == 0 {
        let mut hist: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < bins_y
            invariant
                hist.len() == i,
                i <= bins_y,
                (forall|j: int| 0 <= j < i ==> #[trigger] hist[j].len() == bins_x),
                (forall|j: int, k: int| 0 <= j < i && 0 <= k < bins_x ==> #[trigger] hist[j][k] >= 0),
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < bins_x
                invariant
                    row.len() == j,
                    j <= bins_x,
                    (forall|k: int| 0 <= k < j ==> #[trigger] row[k] >= 0),
            {
                row.push(0);
                j = j + 1;
            }
            hist.push(row);
            i = i + 1;
        }
        let edges_x = create_edges(0, 10, bins_x);
        let edges_y = create_edges(0, 10, bins_y);
        return (hist, edges_x, edges_y);
    }
    
    let mut min_x = sample[0].0;
    let mut max_x = sample[0].0;
    let mut min_y = sample[0].1;
    let mut max_y = sample[0].1;
    
    let mut i: usize = 1;
    while i < sample.len()
        invariant
            i <= sample.len(),
            i > 0,
    {
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
        i = i + 1;
    }
    
    let edges_x = create_edges(min_x, max_x, bins_x);
    let edges_y = create_edges(min_y, max_y, bins_y);
    
    let mut hist: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < bins_y
        invariant
            hist.len() == i,
            i <= bins_y,
            (forall|j: int| 0 <= j < i ==> #[trigger] hist[j].len() == bins_x),
            (forall|j: int, k: int| 0 <= j < i && 0 <= k < bins_x ==> #[trigger] hist[j][k] >= 0),
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < bins_x
            invariant
                row.len() == j,
                j <= bins_x,
                (forall|k: int| 0 <= k < j ==> #[trigger] row[k] >= 0),
        {
            row.push(0);
            j = j + 1;
        }
        hist.push(row);
        i = i + 1;
    }
    
    let mut i: usize = 0;
    while i < sample.len()
        invariant
            i <= sample.len(),
            hist.len() == bins_y,
            (forall|j: int| 0 <= j < bins_y ==> #[trigger] hist[j].len() == bins_x),
            (forall|j: int, k: int| 0 <= j < bins_y && 0 <= k < bins_x ==> #[trigger] hist[j][k] >= 0),
    {
        let x = sample[i].0;
        let y = sample[i].1;
        
        if x >= edges_x[0] && x < edges_x[bins_x] && y >= edges_y[0] && y < edges_y[bins_y] {
            let bin_x = find_bin(x, edges_x.clone());
            let bin_y = find_bin(y, edges_y.clone());
            
            let mut new_row = hist[bin_y].clone();
            new_row.set(bin_x, new_row[bin_x] + 1);
            hist.set(bin_y, new_row);
        }
        i = i + 1;
    }
    
    (hist, edges_x, edges_y)
}
// </vc-code>

}
fn main() {}