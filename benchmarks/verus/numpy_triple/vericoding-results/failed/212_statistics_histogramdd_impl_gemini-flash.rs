// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Cast `bins` to `i32` for `bin_size_den` and `i` to `i32` for multiplication. Also corrected types for `edges` array access to `int` within specs. */
fn calculate_edges(min_val: i32, max_val: i32, bins: usize) -> (edges: Vec<i32>)
    requires
        max_val >= min_val,
        bins > 0,
    ensures
        edges.len() == bins + 1,
        forall|i: int| 0 <= i < bins ==> #[trigger] edges[i] < edges[i + 1],
        edges[0] == min_val,
        edges[bins as int] == max_val
{
    let mut edges = Vec::new();
    let range = max_val - min_val;
    let bin_size_num = range as i32;
    let bin_size_den = bins as i32;

    edges.push(min_val);

    let mut i: usize = 1;
    while i < bins
        invariant
            1 <= i <= bins,
            edges.len() == i,
            forall|j: int| 0 <= j < i - 1 ==> edges[j] < edges[j+1],
            edges[0] == min_val,
            edges[(i - 1) as int] == min_val + (((i - 1) as i32) * bin_size_num / bin_size_den),
        decreases bins - i
    {
        let edge_val = min_val + ((i as i32) * bin_size_num / bin_size_den);
        edges.push(edge_val);
        i = i + 1;
    }
    edges.push(max_val);
    edges
}

fn get_bin_index(value: i32, edges: &Vec<i32>) -> (index: usize)
    requires
        edges.len() > 1,
        forall|i: int| 0 <= i < (edges.len() as int) - 1 ==> #[trigger] edges[i] < edges[i+1],
        value >= edges[0],
        value <= edges[((edges.len()) as int) - 1],
    ensures
        0 <= index < (edges.len() as int) - 1,
        edges[index as int] <= value,
        value < edges[(index + 1) as int] || (index as int == (edges.len() as int) - 2 && value == edges[((edges.len()) as int) - 1])
{
    let mut low: usize = 0;
    let mut high: usize = edges.len() - 2;
    let mut result_index: usize = 0;

    while low <= high
        invariant
            0 <= low,
            high as int <= (edges.len() as int) - 2,
            low as int <= high as int + 1,
            0 <= result_index,
            result_index as int <= (edges.len() as int) - 2,

            // Establish that the answer must be in [low, high] or has been found in result_index
            (low <= high ==> edges[low as int] <= value),
            (high + 1 <= (edges.len() as int) -1 ==> value < edges[(high + 1) as int]),

            // If we've found a result, ensure its validity
            (low > high ==> edges[result_index as int] <= value && (value < edges[(result_index + 1) as int] || (result_index as int == (edges.len() as int) - 2 && value == edges[(edges.len() as int) - 1]))),
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        if edges[mid as int] <= value {
            result_index = mid;
            low = mid + 1;
        } else {
            match mid.checked_sub(1) {
                Some(val) => high = val,
                None => high = 0, // This case should ideally not be reached if low is > 0
            }
        }
    }

    // Handle the upper bound edge case where value == edges.last()
    if is_last(edges, value, result_index) {
        result_index // Already correctly set to the last valid bin
    } else {
        result_index
    }
}

fn is_last(edges: &Vec<i32>, value: i32, result_index: usize) -> (ret: bool)
    requires
        edges.len() > 1,
        result_index as int <= (edges.len() as int) - 1,
    ensures
        (result_index as int == (edges.len() as int) - 2 && value == edges[(edges.len() as int) - 1]) == ret
{
    // Check if result_index refers to the second to last bin and the value is exactly the last edge
    // This correctly places values equal to the last edge into the last bin
    result_index as int == (edges.len() as int) - 2 && value == edges[(edges.len() as int) - 1]
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
/* code modified by LLM (iteration 5): Corrected `bin_size_num` and `bin_size_den` to be `i32` and cast loop variable `i` to `i32` for arithmetic operations. Fixed vector index access types to `int` within conditions. */
{
    let mut min_x = i32::MAX;
    let mut max_x = i32::MIN;
    let mut min_y = i32::MAX;
    let mut max_y = i32::MIN;

    if sample.len() == 0 {
        let hist: Vec<Vec<i32>> = vec![vec![0; bins_x]; bins_y];
        let edges_x = calculate_edges(0, 1, bins_x);
        let edges_y = calculate_edges(0, 1, bins_y);
        return (hist, edges_x, edges_y);
    }

    let mut i = 0;
    while i < sample.len()
        invariant
            0 <= i <= sample.len(),
            (i == 0 ==> min_x == i32::MAX && max_x == i32::MIN && min_y == i32::MAX && max_y == i32::MIN),
            (i > 0 ==> min_x <= max_x && min_y <= max_y),
            forall|j: int| 0 <= j < i ==> #[trigger] min_x <= sample[j].0 && #[trigger] sample[j].0 <= max_x,
            forall|j: int| 0 <= j < i ==> #[trigger] min_y <= sample[j].1 && #[trigger] sample[j].1 <= max_y,
        decreases sample.len() - i
    {
        let (x, y) = sample[i as int];
        if x < min_x { min_x = x; }
        if x > max_x { max_x = x; }
        if y < min_y { min_y = y; }
        if y > max_y { max_y = y; }
        i = i + 1;
    }

    // If all points are identical, ensure a valid range for bin edges
    if min_x == max_x { max_x = max_x + 1; /* For non-empty interval */ }
    if min_y == max_y { max_y = max_y + 1; /* For non-empty interval */ }

    let edges_x = calculate_edges(min_x, max_x, bins_x);
    let edges_y = calculate_edges(min_y, max_y, bins_y);

    let mut hist: Vec<Vec<i32>> = Vec::new();
    let mut r = 0;
    while r < bins_y
        invariant
            0 <= r <= bins_y,
            hist.len() == r,
            forall|k: int| 0 <= k < r ==> hist[k].len() == bins_x,
            forall|k: int, l: int| 0 <= k < r && 0 <= l < bins_x ==> hist[k][l] == 0,
        decreases bins_y - r
    {
        let mut row_vec: Vec<i32> = Vec::new();
        let mut c = 0;
        while c < bins_x
            invariant
                0 <= c <= bins_x,
                row_vec.len() == c,
                forall|k: int| 0 <= k < c ==> row_vec[k] == 0,
            decreases bins_x - c
        {
            row_vec.push(0);
            c = c + 1;
        }
        hist.push(row_vec);
        r = r + 1;
    }

    let mut k = 0;
    while k < sample.len()
        invariant
            0 <= k <= sample.len(),
            hist.len() == bins_y,
            forall|y_idx: int| 0 <= y_idx < bins_y ==> hist[y_idx].len() == bins_x,
            forall|y_idx: int, x_idx: int| 0 <= y_idx < bins_y && 0 <= x_idx < bins_x ==> hist[y_idx][x_idx] >= 0,
            // All previous samples have been correctly binned
            forall|idx: int| 0 <= idx < k ==> {
                let x = sample[idx].0;
                let y = sample[idx].1;
                let x_bin = get_bin_index(x, &edges_x);
                let y_bin = get_bin_index(y, &edges_y);
                true // This invariant is getting complicated, will try to express later
            },
        decreases sample.len() - k
    {
        let (x, y) = sample[k as int];
        let x_bin = get_bin_index(x, &edges_x);
        let y_bin = get_bin_index(y, &edges_y);
        
        hist[y_bin as int][x_bin as int] = hist[y_bin as int][x_bin as int] + 1;
        k = k + 1;
    }

    (hist, edges_x, edges_y)
}
// </vc-code>

}
fn main() {}