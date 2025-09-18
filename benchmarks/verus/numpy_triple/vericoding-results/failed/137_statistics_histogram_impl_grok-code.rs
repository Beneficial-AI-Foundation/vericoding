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

// </vc-helpers>

// <vc-spec>
fn histogram(data: Vec<i32>, n_bins: usize, min_val: i32, max_val: i32) -> (result: (Vec<usize>, Vec<i32>))
    requires
        n_bins > 0,
        min_val < max_val,
    ensures

        result.1.len() == n_bins + 1,
        result.1[0] == min_val,
        result.1[(n_bins as int)] == max_val,

        result.0.len() == n_bins,

        sum_seq(result.0@) == data@.filter(|x: i32| min_val <= x && x <= max_val).len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): change for loop to use supported range */
    let range = (max_val - min_val) as usize;
    let mut counts = std::vec::from_elem(0usize, n_bins);
    let mut bin_edges = std::vec::from_elem(0i32, n_bins + 1);
    
    for i in 0..(n_bins + 1) {
        bin_edges[i] = min_val + ((i as i32) * ((max_val - min_val) + 1) / (n_bins as i32));
    }
    
    for &x in &data {
        if min_val <= x && x <= max_val {
            let bin = (((x - min_val) as usize) * n_bins) / (((max_val - min_val) as usize) + 1);
            counts[bin] += 1;
        }
    }
    
    (counts, bin_edges)
}
// </vc-code>

}
fn main() {}