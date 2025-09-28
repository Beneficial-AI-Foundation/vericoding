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
/* helper modified by LLM (iteration 3): fixed sequence indexing and type conversion */
fn min(a: i8, b: i8) -> i8 { if a < b { a } else { b } }

spec fn in_range(x: i8, min_val: i8, max_val: i8) -> bool {
    (min_val as int) <= (x as int) && (x as int) <= (max_val as int)
}

spec fn find_bin_index(val: i8, bin_edges: Seq<i8>, n_bins: usize) -> int
    decreases n_bins
{
    if n_bins == 0 {
        0
    } else if (val as int) < (bin_edges[1] as int) {
        0
    } else {
        1 + find_bin_index(val, bin_edges.drop_first(), (n_bins - 1) as usize)
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
/* code modified by LLM (iteration 3): fixed loop bounds and indexing */
{
    let mut counts = Vec::new();
    for i in 0..n_bins {
        counts.push(0);
    }
    
    let mut bin_edges = Vec::new();
    bin_edges.push(min_val);
    
    let bin_size_i8 = ((max_val as i16 - min_val as i16) / (n_bins as i16)) as i8;
    
    for i in 1..n_bins {
        let edge = min_val + (i as i8) * bin_size_i8;
        bin_edges.push(edge);
    }
    bin_edges.push(max_val);
    
    for j in 0..data.len() {
        let val = data[j];
        if min_val <= val && val <= max_val {
            let mut bin_idx = 0;
            while bin_idx < n_bins
                invariant
                    0 <= bin_idx && bin_idx <= n_bins,
                    bin_idx == 0 ==> val < bin_edges[0],
                    bin_idx > 0 ==> bin_edges[bin_idx - 1] <= val,
                decreases n_bins - bin_idx
            {
                if bin_idx < n_bins && val >= bin_edges[bin_idx + 1] {
                    bin_idx = bin_idx + 1;
                } else {
                    break;
                }
            }
            if bin_idx < n_bins {
                counts[bin_idx] = counts[bin_idx] + 1;
            }
        }
    }
    
    (counts, bin_edges)
}
// </vc-code>

}
fn main() {}