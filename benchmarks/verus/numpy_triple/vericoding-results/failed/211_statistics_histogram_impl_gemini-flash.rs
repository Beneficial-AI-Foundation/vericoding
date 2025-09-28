// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_seq(s: Seq<usize>) -> nat 
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        (s[0] as nat) + sum_seq(s.drop_first())
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added #[trigger] annotation to fix trigger inference error. */
proof fn lemma_bin_edges(n_bins: usize, min_val: i8, max_val: i8)
    requires
        n_bins > 0,
        (min_val as int) < (max_val as int),
    ensures
        (n_bins as nat) >= 1,
        (max_val as int) - (min_val as int) >= 1,
{
    assert((max_val as int) - (min_val as int) >= 1);
    assert((n_bins as int) >= 1);
}
// </vc-helpers>

// <vc-spec>
fn histogram(data: Vec<i8>, n_bins: usize, min_val: i8, max_val: i8) -> (result: (Vec<usize>, Vec<i8>))
    requires
        n_bins > 0,
        (min_val as int) < (max_val as int),
    ensures

        result.1.len() == n_bins + 1,
        result.1[0] == min_val,
        result.1[(n_bins as int)] == max_val,

        result.0.len() == n_bins,

        sum_seq(result.0@) == data@.filter(|x: i8| (min_val as int) <= (x as int) && (x as int) <= (max_val as int)).len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected monotonicity invariant by adding #[trigger] to the quantifier. */
{
    let mut counts: Vec<usize> = Vec::new();
    counts.resize(n_bins, 0usize);

    let mut edges: Vec<i8> = Vec::new();

    let range_i: i64 = (max_val as i64) - (min_val as i64);
    let n_bins_i: i64 = n_bins as i64;

    // Handle cases where range or n_bins are zero to avoid division by zero or incorrect binning
    let bin_width_i: i64 = if n_bins_i == 0 { 0 } else { range_i / n_bins_i };

    // Calculate bin edges
    edges.push(min_val);
    let mut i = 0;
    while i < n_bins - 1
        invariant
            0 <= i,
            i <= n_bins - 1,
            edges.len() == i + 1,
            edges.len() >= 1,
            edges@[0] == min_val,
            #[trigger](forall|j: int| 0 <= j && j < edges.len() - 1 ==> (edges@[j] as int) <= (edges@[j + 1] as int)),
        decreases n_bins - 1 - i
    {
        let next_edge: i8 = (min_val as i64 + (i as i64 + 1) * bin_width_i) as i8;
        edges.push(next_edge);
        i = i + 1;
    }
    edges.push(max_val);

    // Distribute data into bins
    for val in data.iter() {
        let v_i: i64 = *val as i64;
        if v_i >= (min_val as i64) && v_i <= (max_val as i64) {

            // Special handling for values equal to max_val to be included in the last bin
            let bin_idx: usize;
            if v_i == (max_val as i64) {
                bin_idx = n_bins - 1;
            } else {
                // Calculate bin index based on value and bin edges
                let mut current_bin_idx_i: i64;

                if bin_width_i == 0 {
                    current_bin_idx_i = 0;
                } else {
                    current_bin_idx_i = (v_i - (min_val as i64)) / bin_width_i;
                }
                
                if current_bin_idx_i >= n_bins_i {
                    current_bin_idx_i = n_bins_i - 1;
                }
                if current_bin_idx_i < 0 {
                     current_bin_idx_i = 0; // Should ideally not happen if min_val logic is correct
                }
                bin_idx = current_bin_idx_i as usize;
            }
            counts.set(bin_idx, counts[bin_idx] + 1);
        }
    }
    (counts, edges)
}
// </vc-code>

}
fn main() {}