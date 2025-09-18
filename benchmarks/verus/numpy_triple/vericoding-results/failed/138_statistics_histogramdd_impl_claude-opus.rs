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
    /* code modified by LLM (iteration 5): Fixed mutable indexing issue by using set method */
    let min_x: i32 = if sample.len() == 0 { 0 } else {
        let mut min = sample[0].0;
        for i in 1..sample.len()
            invariant min <= sample[0].0
        {
            if sample[i].0 < min {
                min = sample[i].0;
            }
        }
        min
    };
    
    let max_x: i32 = if sample.len() == 0 { 100 } else {
        let mut max = sample[0].0;
        for i in 1..sample.len()
            invariant max >= sample[0].0
        {
            if sample[i].0 > max {
                max = sample[i].0;
            }
        }
        max
    };
    
    let min_y: i32 = if sample.len() == 0 { 0 } else {
        let mut min = sample[0].1;
        for i in 1..sample.len()
            invariant min <= sample[0].1
        {
            if sample[i].1 < min {
                min = sample[i].1;
            }
        }
        min
    };
    
    let max_y: i32 = if sample.len() == 0 { 100 } else {
        let mut max = sample[0].1;
        for i in 1..sample.len()
            invariant max >= sample[0].1
        {
            if sample[i].1 > max {
                max = sample[i].1;
            }
        }
        max
    };
    
    let range_x = (max_x - min_x) as usize;
    let range_y = (max_y - min_y) as usize;
    
    let mut edges_x: Vec<i32> = Vec::new();
    for i in 0..(bins_x + 1)
        invariant
            edges_x.len() == i,
            forall|j: int| 0 <= j < i - 1 ==> #[trigger] edges_x[j] < edges_x[j + 1]
    {
        let edge = min_x + (range_x * i / bins_x) as i32;
        edges_x.push(edge);
    }
    
    let mut edges_y: Vec<i32> = Vec::new();
    for i in 0..(bins_y + 1)
        invariant
            edges_y.len() == i,
            forall|j: int| 0 <= j < i - 1 ==> #[trigger] edges_y[j] < edges_y[j + 1]
    {
        let edge = min_y + (range_y * i / bins_y) as i32;
        edges_y.push(edge);
    }
    
    let mut hist: Vec<Vec<i32>> = Vec::new();
    for i in 0..bins_y
        invariant
            hist.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] hist[j].len() == bins_x,
            forall|j: int, k: int| 0 <= j < i && 0 <= k < bins_x ==> #[trigger] hist[j][k] >= 0
    {
        let mut row: Vec<i32> = Vec::new();
        for j in 0..bins_x
            invariant
                row.len() == j,
                forall|k: int| 0 <= k < j ==> #[trigger] row[k] >= 0
        {
            row.push(0i32);
        }
        hist.push(row);
    }
    
    for k in 0..sample.len()
        invariant
            hist.len() == bins_y,
            forall|i: int| 0 <= i < bins_y ==> #[trigger] hist[i].len() == bins_x,
            forall|i: int, j: int| 0 <= i < bins_y && 0 <= j < bins_x ==> #[trigger] hist[i][j] >= 0
    {
        let (x, y) = sample[k];
        let mut bin_x = 0usize;
        for i in 0..bins_x {
            if x >= edges_x[i] && x < edges_x[i + 1] {
                bin_x = i;
                break;
            }
        }
        let mut bin_y = 0usize;
        for i in 0..bins_y {
            if y >= edges_y[i] && y < edges_y[i + 1] {
                bin_y = i;
                break;
            }
        }
        if bin_x < bins_x && bin_y < bins_y {
            let old_val = hist[bin_y][bin_x];
            hist[bin_y].set(bin_x, old_val + 1);
        }
    }
    
    (hist, edges_x, edges_y)
}
// </vc-code>

}
fn main() {}