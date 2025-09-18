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
/* helper modified by LLM (iteration 4): Fixed type mismatch in bin_index by casting n_bins to int */
spec fn bin_index(x: i32, min_val: i32, max_val: i32, n_bins: usize) -> int
    requires
        min_val < max_val,
        n_bins > 0,
        min_val <= x && x <= max_val,
    ensures
        0 <= bin_index(x, min_val, max_val, n_bins) < n_bins as int,
{
    let range = max_val - min_val;
    let bin_size = (range / (n_bins as int)) as nat;
    if x == max_val {
        (n_bins - 1) as int
    } else {
        if bin_size == 0 {
            if x == min_val {
                0
            } else {
                if n_bins == 1 {
                    0
                } else {
                    1
                }
            }
        } else {
            ((x - min_val) as nat / bin_size) as int
        }
    }
}

proof fn sum_seq_filter(s: Seq<i32>, min_val: i32, max_val: i32) -> (sum: nat)
    ensures
        sum == s.filter(|x: i32| min_val <= x && x <= max_val).len(),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.filter(|x: i32| min_val <= x && x <= max_val).len() == 0);
        0
    } else {
        let filtered_tail = s.drop_first().filter(|x: i32| min_val <= x && x <= max_val);
        let tail_sum = sum_seq_filter(s.drop_first(), min_val, max_val);
        if min_val <= s[0] && s[0] <= max_val {
            assert(s.filter(|x: i32| min_val <= x && x <= max_val) =~= seq![s[0]] + filtered_tail);
            tail_sum + 1
        } else {
            assert(s.filter(|x: i32| min_val <= x && x <= max_val) =~= filtered_tail);
            tail_sum
        }
    }
}

fn compute_bin_index(x: i32, min_val: i32, max_val: i32, n_bins: usize) -> usize
    requires
        min_val < max_val,
        n_bins > 0,
        min_val <= x && x <= max_val,
    ensures
        0 <= compute_bin_index(x, min_val, max_val, n_bins) < n_bins as int,
{
    let range = max_val - min_val;
    let bin_size = range / (n_bins as i32);
    if x == max_val {
        n_bins - 1
    } else {
        if bin_size == 0 {
            if x == min_val {
                0
            } else {
                if n_bins == 1 {
                    0
                } else {
                    1
                }
            }
        } else {
            let offset = x - min_val;
            let index = offset / bin_size;
            index as usize
        }
    }
}
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
/* code modified by LLM (iteration 4): No changes, code remains the same as iteration 3 */
{
    let mut counts = vec![0usize; n_bins];
    let mut bin_edges = Vec::with_capacity(n_bins + 1);
    
    // Calculate and set bin edges
    let bin_size = (max_val - min_val) / (n_bins as i32);
    bin_edges.push(min_val);
    let mut current = min_val;
    for _ in 1..n_bins {
        current = current + bin_size;
        bin_edges.push(current);
    }
    bin_edges.push(max_val);
    
    // Count elements in each bin
    for j in 0..data.len()
        invariant
            counts.len() == n_bins,
            bin_edges.len() == n_bins + 1,
            bin_edges[0] == min_val,
            bin_edges[(n_bins as int)] == max_val,
    {
        let val = data[j];
        if min_val <= val && val <= max_val {
            let bin_idx = compute_bin_index(val, min_val, max_val, n_bins);
            counts[bin_idx] = counts[bin_idx] + 1;
        }
    }
    
    // Prove the sum of counts equals the number of filtered elements
    proof {
        sum_seq_filter(data@, min_val, max_val);
    }
    
    (counts, bin_edges)
}
// </vc-code>

}
fn main() {}