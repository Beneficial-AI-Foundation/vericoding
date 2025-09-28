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
/* helper modified by LLM (iteration 5): Removed f64 casting, using pure i8 arithmetic */
spec fn bin_edges_valid(edges: Seq<i8>, n_bins: usize, min_val: i8, max_val: i8) -> bool {
    edges.len() == n_bins + 1 &&
    edges[0] == min_val &&
    edges[n_bins as int] == max_val &&
    forall|i: int| 0 <= i < n_bins ==> edges[i] <= edges[i + 1]
}

spec fn in_range(val: i8, min_val: i8, max_val: i8) -> bool {
    (min_val as int) <= (val as int) && (val as int) <= (max_val as int)
}

spec fn find_bin_index(val: i8, edges: Seq<i8>, n_bins: usize) -> int {
    if n_bins == 0 {
        -1
    } else if (val as int) < (edges[0] as int) {
        -1
    } else if (val as int) > (edges[n_bins as int] as int) {
        -1
    } else {
        (choose|i: int| 0 <= i < n_bins && (edges[i] as int) <= (val as int) && (val as int) <= (edges[i + 1] as int))
    }
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
{
    /* code modified by LLM (iteration 5): Removed f64 casting, using i8 arithmetic only */
    let mut edges: Vec<i8> = Vec::new();
    let mut i = 0;
    
    while i <= n_bins
        invariant
            i <= n_bins + 1,
            edges.len() == i,
        decreases n_bins + 1 - i
    {
        if i == 0 {
            edges.push(min_val);
        } else if i == n_bins {
            edges.push(max_val);
        } else {
            let range_width = (max_val as int) - (min_val as int);
            let edge_val = (min_val as int) + ((i as int) * range_width) / (n_bins as int);
            edges.push(edge_val as i8);
        }
        i = i + 1;
    }
    
    let mut counts: Vec<usize> = Vec::new();
    let mut j = 0;
    
    while j < n_bins
        invariant
            j <= n_bins,
            counts.len() == j,
        decreases n_bins - j
    {
        counts.push(0);
        j = j + 1;
    }
    
    let mut k = 0;
    
    while k < data.len()
        invariant
            k <= data.len(),
            counts.len() == n_bins,
            edges.len() == n_bins + 1,
        decreases data.len() - k
    {
        let val = data[k];
        if in_range(val, min_val, max_val) {
            let mut bin_idx = 0;
            while bin_idx < n_bins && (val as int) > (edges[bin_idx + 1] as int)
                invariant
                    bin_idx <= n_bins,
                    counts.len() == n_bins,
                decreases n_bins - bin_idx
            {
                bin_idx = bin_idx + 1;
            }
            if bin_idx < n_bins {
                counts.set(bin_idx, counts[bin_idx] + 1);
            }
        }
        k = k + 1;
    }
    
    (counts, edges)
}
// </vc-code>

}
fn main() {}