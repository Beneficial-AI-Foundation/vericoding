// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected indexing for `Seq` and type comparison */
fn min_vec(vec: Seq<i32>) -> (min: i32)
    requires
        vec.len() > 0,
    ensures
        (exists|i: int| 0 <= i < vec.len() && vec[i] == min) &&
        (forall|i: int| 0 <= i < vec.len() ==> vec[i] >= min)
{
    let mut min_val = vec.trigger_builtin_index(0);
    let mut i: int = 1;
    while i < vec.len()
        invariant
            0 <= i <= vec.len(),
            (exists|j: int| 0 <= j < i && vec[j] == min_val) &&
            (forall|j: int| 0 <= j < i ==> vec[j] >= min_val)
    {
        if vec.trigger_builtin_index(i) < min_val {
            min_val = vec.trigger_builtin_index(i);
        }
        i = i + 1;
    }
    min_val
}

fn max_vec(vec: Seq<i32>) -> (max: i32)
    requires
        vec.len() > 0,
    ensures
        (exists|i: int| 0 <= i < vec.len() && vec[i] == max) &&
        (forall|i: int| 0 <= i < vec.len() ==> vec[i] <= max)
{
    let mut max_val = vec.trigger_builtin_index(0);
    let mut i: int = 1;
    while i < vec.len()
        invariant
            0 <= i <= vec.len(),
            (exists|j: int| 0 <= j < i && vec[j] == max_val) &&
            (forall|j: int| 0 <= j < i ==> vec[j] <= max_val)
    {
        if vec.trigger_builtin_index(i) > max_val {
            max_val = vec.trigger_builtin_index(i);
        }
        i = i + 1;
    }
    max_val
}

fn calculate_edges(min_val: i32, max_val: i32, bins: usize) -> (edges: Vec<i32>)
    requires
        bins > 0,
    ensures
        edges.len() == bins + 1,
        (forall|i: int| 0 <= i < bins ==> edges[i] < edges[i + 1]),
        edges[0] == min_val
{
    if min_val == max_val {
        let mut edges = Vec::new();
        edges.push(min_val);
        for i in 1..bins + 1 {
            edges.push(min_val + 1);
        }
        return edges;
    }
    
    let range = (max_val - min_val) as i32;
    let step_size = if bins > 0 { range / (bins as i32) } else { 1 };
    let mut edges = Vec::new();
    edges.push(min_val);

    let mut i = 0;
    while i < bins
        invariant
            i <= bins,
            edges.len() == i + 1,
            (forall|j: int| 0 <= j < i ==> edges[j] < edges[j + 1]),
            edges[0] == min_val
    {
        if i == bins - 1 {
            edges.push(max_val);
        } else {
            edges.push(min_val + step_size * (i as i32 + 1));
        }
        i = i + 1;
    }
    
    let mut final_edges = Vec::new();
    final_edges.push(edges[0]);
    let mut k: int = 0;
    while k < (bins as int)
        invariant
            k < bins as int,
            final_edges.len() == k + 1,
            (forall|j: int| 0 <= j < k ==> final_edges[j] < final_edges[j + 1]),
            final_edges[0] == min_val
    {
        let next_edge = edges.trigger_builtin_index(k as usize + 1);
        if next_edge <= final_edges.trigger_builtin_index(k as usize) {
            final_edges.push(final_edges.trigger_builtin_index(k as usize) + 1);
        } else {
            final_edges.push(next_edge);
        }
        k = k + 1;
    }
    if final_edges.trigger_builtin_index(bins) < max_val {
        final_edges.pop();
        final_edges.push(max_val);
    }

    final_edges
}

fn find_bin_index_internal(value: i32, edges: &[i32]) -> (idx: usize)
    requires
        edges.len() >= 2,
        (forall|i: int| 0 <= i < (edges.len() as int) - 1 ==> #[trigger] edges[i] < edges[i + 1])
    ensures
        0 <= idx < edges.len() - 1,
        edges[idx] <= value,
        value < edges[idx + 1] || (idx == edges.len() - 2 && value == edges[edges.len() - 1])
{
    let mut low: usize = 0;
    let mut high: usize = edges.len() - 1;
    let mut result_idx: usize = 0;

    while low <= high
        invariant
            low <= edges.len(),
            high <= edges.len(),
            result_idx < edges.len(),
            low <= high + 1
    {
        let mid = low + (high - low) / 2;

        if edges[mid] <= value {
            result_idx = mid;
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }

    if result_idx >= edges.len() - 1 && edges.len() > 1 && value >= edges[edges.len() - 1] {
        result_idx = edges.len() - 2;
    } else if result_idx > 0 && value < edges[result_idx] {
        result_idx = result_idx - 1;
    }
    

    result_idx
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
/* code modified by LLM (iteration 5): Corrected type mismatches between integer and nat. */
{
    let mut all_x_coords: Vec<i32> = Vec::new();
    let mut all_y_coords: Vec<i32> = Vec::new();

    if sample.len() == (0 as usize) {
        let mut hist: Vec<Vec<i32>> = Vec::new();
        for _ in 0..bins_y {
            let mut row = Vec::new();
            for _ in 0..bins_x {
                row.push(0);
            }
            hist.push(row);
        }

        let mut edges_x = Vec::new();
        for i in 0..bins_x + 1 {
            edges_x.push(0);
        }
        let mut edges_y = Vec::new();
        for i in 0..bins_y + 1 {
            edges_y.push(0);
        }
        return (hist, edges_x, edges_y);
    }

    for i in (0 as usize)..sample.len() {
        let (x, y) = sample.get(i as usize).unwrap();
        all_x_coords.push(*x);
        all_y_coords.push(*y);
        proof {
            all_x_coords@.push(*x);
            all_y_coords@.push(*y);
        }
    }

    let min_x = min_vec(all_x_coords@);
    let max_x = max_vec(all_x_coords@);
    let min_y = min_vec(all_y_coords@);
    let max_y = max_vec(all_y_coords@);

    let edges_x = calculate_edges(min_x, max_x, bins_x);
    let edges_y = calculate_edges(min_y, max_y, bins_y);

    let mut hist: Vec<Vec<i32>> = Vec::new();
    for _ in 0..bins_y {
        let mut row = Vec::new();
        for _ in 0..bins_x {
            row.push(0);
        }
        hist.push(row);
    }

    for i in (0 as usize)..sample.len() {
        let (x, y) = sample.get(i as usize).unwrap();
        let x_idx = find_bin_index_internal(*x, edges_x.as_slice());
        let y_idx = find_bin_index_internal(*y, edges_y.as_slice());

        *hist.get_mut(y_idx).unwrap().get_mut(x_idx).unwrap() += 1;
    }

    (hist, edges_x, edges_y)
}
// </vc-code>

}
fn main() {}