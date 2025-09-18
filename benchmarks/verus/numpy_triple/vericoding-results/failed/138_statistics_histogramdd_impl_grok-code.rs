// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn calculate_bin_edges(min_val: i32, max_val: i32, bins: usize) -> (result: Vec<i32>)
    requires
        bins > 0,
        min_val < max_val,
    ensures
        result.len() == bins + 1,
        (forall|i: int| 0 <= i < bins ==> #[trigger] result[i] < result[i + 1]),
        result[0] == min_val,
        result[bins] == max_val;

proof fn lemma_bin_edges_sorted(edges: Vec<i32>, bins: usize)
    requires
        edges.len() == bins + 1,
        (forall|i: int| 0 <= i < bins ==> #[trigger] edges[i] < edges[i + 1]),
    ensures
        edges@[0] < edges@[bins],
    decreases bins
{
    if bins > 0 {
        lemma_bin_edges_sorted(edges, bins - 1);
    }
}

fn find_bin_index(value: i32, edges: Vec<i32>) -> (result: usize)
    requires
        edges.len() > 1,
        (forall|i: int| 0 <= i < edges.len() - 1 ==> edges[i] < edges[i + 1]),
        edges[0] <= value <= edges[edges.len() - 1],
    ensures
        result < edges.len() - 1,
        edges[result] <= value <= edges[result + 1],
{
    let mut low = 0;
    let mut high = edges.len() - 1;
    while low < high {
        let mid = (low + high) / 2;
        if edges[mid] > value {
            high = mid;
        } else if edges[mid + 1] <= value {
            low = mid + 1;
        } else {
            return mid;
        }
    }
    low
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
    let mut hist: Vec<Vec<i32>> = Vec::with_capacity(bins_y);
    for _i in 0..bins_y {
        hist.push(Vec::with_capacity(bins_x));
        for _j in 0..bins_x {
            hist[i].push(0);
        }
    }
    let x_values: Seq<i32> = sample.map(|p| p.0);
    let y_values: Seq<i32> = sample.map(|p| p.1);
    let min_x = if x_values.is_empty() { 0 } else { x_values.index(0) };
    for value in x_values {
        min_x = if value < min_x { value } else { min_x };
    }
    let max_x = if x_values.is_empty() { 1 } else { x_values.index(0) };
    for value in x_values {
        max_x = if value > max_x { value } else { max_x };
    }
    let min_y = if y_values.is_empty() { 0 } else { y_values.index(0) };
    for value in y_values {
        min_y = if value < min_y { value } else { min_y };
    }
    let max_y = if y_values.is_empty() { 1 } else { y_values.index(0) };
    for value in y_values {
        max_y = if value > max_y { value } else { max_y };
    }
    let edges_x = calculate_bin_edges(min_x, max_x, bins_x);
    let edges_y = calculate_bin_edges(min_y, max_y, bins_y);
    let mut i = 0;
    while i < sample.len() {
        invariant
            0 <= i <= sample.len(),
        ;
        let point = sample[i];
        let x_bin = find_bin_index(point.0, edges_x);
        let y_bin = find_bin_index(point.1, edges_y);
        hist[y_bin][x_bin] = hist[y_bin][x_bin] + 1;
        i = i + 1;
    }
    (hist, edges_x, edges_y)
}
// </vc-code>

}
fn main() {}