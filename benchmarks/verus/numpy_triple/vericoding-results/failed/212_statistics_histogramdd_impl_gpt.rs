// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn make_row(n: usize) -> (v: Vec<i32>)
    ensures
        v.len() == n,
        forall|i:int| 0 <= i < n ==> #[trigger] v[i] >= 0,
{
    let mut v: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            v.len() == k,
            forall|i:int| 0 <= i < k ==> #[trigger] v[i] == 0,
        decreases n - k
    {
        v.push(0);
        k += 1;
    }
    v
}

fn make_increasing_edges(n: usize) -> (v: Vec<i32>)
    ensures
        v.len() == n + 1,
        forall|i:int| 0 <= i < n ==> #[trigger] v[i] < v[i + 1],
{
    let mut v: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k <= n
        invariant
            v.len() == k,
            k <= n + 1,
            forall|i:int| 0 <= i < k - 1 ==> #[trigger] v[i] < v[i + 1],
        decreases n - k
    {
        v.push((k as int) as i32);
        k += 1;
    }
    v
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
    let edges_x = make_increasing_edges(bins_x);
    let edges_y = make_increasing_edges(bins_y);

    let mut hist: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;
    while r < bins_y
        invariant
            hist.len() == r,
            r <= bins_y,
            forall|i:int| 0 <= i < r ==> #[trigger] hist[i].len() == bins_x,
            forall|i:int, j:int| 0 <= i < r && 0 <= j < bins_x ==> #[trigger] hist[i][j] >= 0,
        decreases bins_y - r
    {
        let row = make_row(bins_x);
        hist.push(row);
        r += 1;
    }

    (hist, edges_x, edges_y)
}
// </vc-code>

}
fn main() {}