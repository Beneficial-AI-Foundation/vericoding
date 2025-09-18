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
spec fn bin_for_value(value: i32, min_val: i32, max_val: i32, n_bins: usize) -> nat {
    if value < min_val || n_bins == 0 || min_val >= max_val {
        n_bins as nat
    } else if value >= max_val {
        (n_bins - 1) as nat
    } else {
        let range = (max_val - min_val) as nat;
        let bin_width = range / (n_bins as nat);
        let offset = (value - min_val) as nat;
        let bin = offset / bin_width;
        if bin >= n_bins as nat { (n_bins - 1) as nat } else { bin }
    }
}

/* helper modified by LLM (iteration 5): fixed sum_seq_push_lemma to handle recursive case properly */
proof fn sum_seq_push_lemma(s: Seq<usize>, x: usize)
    ensures sum_seq(s.push(x)) == sum_seq(s) + x as nat
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.push(x) =~= seq![x]);
        assert(sum_seq(seq![x]) == x as nat);
    } else {
        let first = s[0];
        let rest = s.drop_first();
        assert(s.push(x) =~= seq![first].add(rest.push(x)));
        assert(sum_seq(s.push(x)) == first as nat + sum_seq(rest.push(x)));
        sum_seq_push_lemma(rest, x);
        assert(sum_seq(rest.push(x)) == sum_seq(rest) + x as nat);
        assert(sum_seq(s) == first as nat + sum_seq(rest));
        assert(sum_seq(s.push(x)) == first as nat + sum_seq(rest) + x as nat);
        assert(sum_seq(s.push(x)) == sum_seq(s) + x as nat);
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
/* code modified by LLM (iteration 5): fixed arithmetic overflow issues and edge initialization */
{
    let mut counts = Vec::new();
    let mut i = 0usize;
    while i < n_bins
        invariant
            i <= n_bins,
            counts.len() == i,
            forall|j: int| 0 <= j < i ==> counts[j] == 0,
        decreases n_bins - i
    {
        counts.push(0usize);
        i = i + 1;
    }
    
    let mut edges = Vec::new();
    
    assert(max_val > min_val);
    let range = (max_val - min_val) as usize;
    let bin_width = range / n_bins;
    
    let mut i = 0usize;
    while i <= n_bins
        invariant
            i <= n_bins + 1,
            edges.len() == i,
            i > 0 ==> edges[0] == min_val,
            forall|j: int| 0 <= j < i && j < n_bins ==> edges[j] == min_val + (j * bin_width) as i32,
            i == n_bins + 1 ==> edges[n_bins as int] == max_val,
        decreases n_bins + 1 - i
    {
        if i == n_bins {
            edges.push(max_val);
        } else {
            let edge_val = min_val + ((i * bin_width) as i32);
            edges.push(edge_val);
        }
        i = i + 1;
    }
    
    assert(edges[0] == min_val);
    assert(edges[n_bins as int] == max_val);
    
    let mut j = 0usize;
    while j < data.len()
        invariant
            j <= data.len(),
            counts.len() == n_bins,
            edges.len() == n_bins + 1,
            edges[0] == min_val,
            edges[n_bins as int] == max_val,
        decreases data.len() - j
    {
        let val = data[j];
        if val >= min_val && val <= max_val {
            let mut bin_idx = 0usize;
            if val >= max_val {
                bin_idx = (n_bins - 1) as usize;
            } else {
                assert(val < max_val);
                assert(val >= min_val);
                let offset = (val - min_val) as usize;
                bin_idx = (offset * n_bins) / range;
                if bin_idx >= n_bins {
                    bin_idx = (n_bins - 1) as usize;
                }
            }
            counts.set(bin_idx, counts[bin_idx] + 1);
        }
        j = j + 1;
    }
    
    (counts, edges)
}
// </vc-code>

}
fn main() {}