// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn find_min_max(sample: &Vec<(i32, i32)>) -> (result: (i32, i32, i32, i32))
    requires
        sample.len() > 0,
    ensures
        ({
            let (min_x, max_x, min_y, max_y) = result;
            min_x <= max_x &&
            min_y <= max_y &&
            (forall|i: int| 0 <= i < sample.len() ==> min_x <= #[trigger] sample[i].0 <= max_x) &&
            (forall|i: int| 0 <= i < sample.len() ==> min_y <= #[trigger] sample[i].1 <= max_y) &&
            (exists|i: int| 0 <= i < sample.len() && #[trigger] sample[i].0 == min_x) &&
            (exists|i: int| 0 <= i < sample.len() && #[trigger] sample[i].0 == max_x) &&
            (exists|i: int| 0 <= i < sample.len() && #[trigger] sample[i].1 == min_y) &&
            (exists|i: int| 0 <= i < sample.len() && #[trigger] sample[i].1 == max_y)
        })
{
    let mut min_x = sample[0].0;
    let mut max_x = sample[0].0;
    let mut min_y = sample[0].1;
    let mut max_y = sample[0].1;
    
    let mut i = 1;
    while i < sample.len()
        invariant
            1 <= i <= sample.len(),
            min_x <= max_x,
            min_y <= max_y,
            (forall|j: int| 0 <= j < i ==> min_x <= #[trigger] sample[j].0 <= max_x),
            (forall|j: int| 0 <= j < i ==> min_y <= #[trigger] sample[j].1 <= max_y),
            (exists|j: int| 0 <= j < i && #[trigger] sample[j].0 == min_x),
            (exists|j: int| 0 <= j < i && #[trigger] sample[j].0 == max_x),
            (exists|j: int| 0 <= j < i && #[trigger] sample[j].1 == min_y),
            (exists|j: int| 0 <= j < i && #[trigger] sample[j].1 == max_y),
        decreases sample.len() - i
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
        i += 1;
    }
    
    (min_x, max_x, min_y, max_y)
}

fn compute_bin_index(value: i32, min_val: i32, max_val: i32, bins: usize) -> (result: usize)
    requires
        bins > 0,
        min_val <= value <= max_val,
    ensures
        result < bins,
{
    if value == max_val {
        bins - 1
    } else {
        let range = max_val - min_val;
        if range == 0 {
            0
        } else {
            let bin_width = range / (bins as i32);
            if bin_width <= 0 {
                0
            } else {
                let idx = (value - min_val) / bin_width;
                if idx >= bins as i32 {
                    bins - 1
                } else {
                    idx as usize
                }
            }
        }
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
{
    /* code modified by LLM (iteration 5): fix vector modification using proper indexing */
    if sample.len() == 0 {
        let mut hist: Vec<Vec<i32>> = Vec::new();
        let mut i = 0;
        while i < bins_y
            invariant
                0 <= i <= bins_y,
                hist.len() == i,
                (forall|j: int| 0 <= j < i ==> #[trigger] hist[j].len() == bins_x),
            decreases bins_y - i
        {
            let mut row = Vec::new();
            let mut j = 0;
            while j < bins_x
                invariant
                    0 <= j <= bins_x,
                    row.len() == j,
                decreases bins_x - j
            {
                row.push(0);
                j += 1;
            }
            hist.push(row);
            i += 1;
        }
        
        let mut edges_x: Vec<i32> = Vec::new();
        let mut k = 0;
        while k <= bins_x
            invariant
                0 <= k <= bins_x + 1,
                edges_x.len() == k,
                (forall|l: int| 0 <= l < k - 1 ==> #[trigger] edges_x[l] < edges_x[l + 1]),
            decreases bins_x + 1 - k
        {
            edges_x.push(k as i32);
            k += 1;
        }
        
        let mut edges_y: Vec<i32> = Vec::new();
        let mut m = 0;
        while m <= bins_y
            invariant
                0 <= m <= bins_y + 1,
                edges_y.len() == m,
                (forall|n: int| 0 <= n < m - 1 ==> #[trigger] edges_y[n] < edges_y[n + 1]),
            decreases bins_y + 1 - m
        {
            edges_y.push(m as i32);
            m += 1;
        }
        
        return (hist, edges_x, edges_y);
    }
    
    let (min_x, max_x, min_y, max_y) = find_min_max(&sample);
    
    let mut hist: Vec<Vec<i32>> = Vec::new();
    let mut i = 0;
    while i < bins_y
        invariant
            0 <= i <= bins_y,
            hist.len() == i,
            (forall|j: int| 0 <= j < i ==> #[trigger] hist[j].len() == bins_x),
        decreases bins_y - i
    {
        let mut row = Vec::new();
        let mut j = 0;
        while j < bins_x
            invariant
                0 <= j <= bins_x,
                row.len() == j,
            decreases bins_x - j
        {
            row.push(0);
            j += 1;
        }
        hist.push(row);
        i += 1;
    }
    
    let mut edges_x: Vec<i32> = Vec::new();
    let mut k = 0;
    while k <= bins_x
        invariant
            0 <= k <= bins_x + 1,
            edges_x.len() == k,
            (forall|l: int| 0 <= l < k - 1 ==> #[trigger] edges_x[l] < edges_x[l + 1]),
        decreases bins_x + 1 - k
    {
        let edge_val = min_x + (k as i32) * ((max_x - min_x) / (bins_x as i32) + 1);
        edges_x.push(edge_val);
        k += 1;
    }
    
    let mut edges_y: Vec<i32> = Vec::new();
    let mut m = 0;
    while m <= bins_y
        invariant
            0 <= m <= bins_y + 1,
            edges_y.len() == m,
            (forall|n: int| 0 <= n < m - 1 ==> #[trigger] edges_y[n] < edges_y[n + 1]),
        decreases bins_y + 1 - m
    {
        let edge_val = min_y + (m as i32) * ((max_y - min_y) / (bins_y as i32) + 1);
        edges_y.push(edge_val);
        m += 1;
    }
    
    let mut idx = 0;
    while idx < sample.len()
        invariant
            0 <= idx <= sample.len(),
            hist.len() == bins_y,
            (forall|i: int| 0 <= i < hist.len() ==> #[trigger] hist[i].len() == bins_x),
            (forall|i: int, j: int| 0 <= i < bins_y && 0 <= j < bins_x ==> #[trigger] hist[i][j] >= 0),
        decreases sample.len() - idx
    {
        let bin_x = compute_bin_index(sample[idx].0, min_x, max_x, bins_x);
        let bin_y = compute_bin_index(sample[idx].1, min_y, max_y, bins_y);
        let old_val = hist[bin_y][bin_x];
        hist.get_mut(bin_y).get_mut(bin_x).set(old_val + 1);
        idx += 1;
    }
    
    (hist, edges_x, edges_y)
}
// </vc-code>

}
fn main() {}