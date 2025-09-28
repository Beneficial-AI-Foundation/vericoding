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
/* helper modified by LLM (iteration 4): Fix ghost code usage by removing invalid int operations */

// Helper for finding the bin index of a value in the histogram
spec fn find_bin_index(value: i8, min_val: i8, max_val: i8, n_bins: usize, bin_edges: Seq<i8>) -> (index: usize)
    requires
        n_bins > 0,
        (min_val as int) < (max_val as int),
        bin_edges.len() == n_bins + 1,
        bin_edges[0] == min_val,
        bin_edges[n_bins] == max_val,
        forall|i: int| 0 <= i < (n_bins as int) ==> (bin_edges[i] as int) < (bin_edges[i+1] as int),
        (min_val as int) <= (value as int) && (value as int) <= (max_val as int)
    ensures
        0 <= index <= n_bins,
        (bin_edges[index] as int) <= (value as int) < (bin_edges[index+1] as int)
{
    let value_int = value as int;
    let min_int = min_val as int;
    let max_int = max_val as int;
    let bin_width_spec = (max_int - min_int) / (n_bins as int);
    ((value_int - min_int) / bin_width_spec) as usize
}

// Helper to calculate bin edges uniformly
spec fn uniform_bin_edges(min_val: i8, max_val: i8, n_bins: usize) -> (edges: Seq<i8>)
    requires
        n_bins > 0,
        (min_val as int) < (max_val as int)
    ensures
        edges.len() == n_bins + 1,
        edges[0] == min_val,
        edges[n_bins] == max_val,
        forall|i: int| 0 <= i < (n_bins as int) ==> 
            (edges[i+1] as int) == (edges[i] as int) + (((max_val as int) - (min_val as int)) / (n_bins as int))
{
    let min_int = min_val as int;
    let max_int = max_val as int;
    let bin_width_spec = (max_int - min_int) / (n_bins as int);
    let mut edges = Seq::<i8>::empty();
    let mut i = 0;
    while i <= n_bins
        invariant
            0 <= i <= n_bins + 1,
            edges.len() == i,
            forall|j: int| 0 <= j < i ==> (edges[j] as int) == min_int + j * bin_width_spec,
            i == 0 || edges[i-1] == if i-1 == n_bins { max_val } else { (min_int + (i-1) * bin_width_spec) as i8 }
    {
        let edge_val = if i == n_bins {
            max_val
        } else {
            (min_int + i * bin_width_spec) as i8
        };
        edges = edges.push(edge_val);
        i += 1;
    }
    edges
}

// Proof helper for sum_seq properties
proof fn sum_seq_appended(s: Seq<usize>, x: usize) -> (total: nat)
    ensures
        total == sum_seq(s.push(x)),
        total == sum_seq(s) + (x as nat)
{
    if s.len() == 0 {
        assert(sum_seq(s.push(x)) == x as nat);
    } else {
        assert(sum_seq(s.push(x)) == (s[0] as nat) + sum_seq(s.drop_first().push(x)));
        let inner_total = sum_seq_appended(s.drop_first(), x);
        assert(sum_seq(s.push(x)) == (s[0] as nat) + inner_total);
        assert(inner_total == sum_seq(s.drop_first()) + (x as nat));
        assert(sum_seq(s) == (s[0] as nat) + sum_seq(s.drop_first()));
    }
    sum_seq(s.push(x))
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
/* code modified by LLM (iteration 4): Fix compilation error by using proper integer operations */
{
    let min_int = min_val as i32;
    let max_int = max_val as i32;
    let bin_width = ((max_int - min_int) / (n_bins as i32)) as i32;
    let mut bin_edges = Vec::<i8>::new();
    let mut bin_counts = Vec::<usize>::new();
    
    // Initialize bin edges
    let mut i: usize = 0;
    while i <= n_bins
        invariant
            0 <= i <= n_bins + 1,
            bin_edges@.len() == i,
            bin_edges@ == uniform_bin_edges(min_val, max_val, n_bins).take(i),
            forall|j: int| 0 <= j < i ==> (bin_edges@[j] as int) == (min_val as int) + j * ((max_val as int) - (min_val as int)) / (n_bins as int),
            i == 0 || bin_edges@[i-1] == if i-1 == n_bins { max_val } else { ((min_val as i32) + ((i-1) as i32) * bin_width) as i8 }
    {
        let edge_val = if i == n_bins {
            max_val
        } else {
            (min_int + (i as i32) * bin_width) as i8
        };
        bin_edges.push(edge_val);
        i += 1;
    }
    
    // Initialize bin counts to zero
    let mut j: usize = 0;
    while j < n_bins
        invariant
            0 <= j <= n_bins,
            bin_counts@.len() == j,
            forall|k: int| 0 <= k < j ==> bin_counts@[k] == 0,
            sum_seq(bin_counts@) == 0
    {
        bin_counts.push(0);
        j += 1;
    }
    
    // Count values in each bin
    let mut k: usize = 0;
    while k < data.len()
        invariant
            0 <= k <= data.len(),
            bin_counts@.len() == n_bins,
            bin_edges@.len() == n_bins + 1,
            forall|m: int| 0 <= m < n_bins ==> (bin_counts@[m] as int) == data@.take(k).filter(|x| 
                (bin_edges@[m] as int) <= (x as int) && (x as int) < (bin_edges@[m+1] as int)).len(),
            sum_seq(bin_counts@) == data@.take(k).filter(|x| (min_val as int) <= (x as int) && (x as int) <= (max_val as int)).len()
        decreases data.len() - k
    {
        let value = data[k];
        let value_int = value as i32;
        if min_int <= value_int && value_int <= max_int {
            let bin_index_i32 = (value_int - min_int) / bin_width;
            if bin_index_i32 < 0 {
                bin_counts.set(0, bin_counts[0] + 1);
            } else if bin_index_i32 >= (n_bins as i32) {
                bin_counts.set(n_bins - 1, bin_counts[n_bins - 1] + 1);
            } else {
                bin_counts.set(bin_index_i32 as usize, bin_counts[bin_index_i32 as usize] + 1);
            }
        }
        k += 1;
    }
    
    (bin_counts, bin_edges)
}
// </vc-code>

}
fn main() {}