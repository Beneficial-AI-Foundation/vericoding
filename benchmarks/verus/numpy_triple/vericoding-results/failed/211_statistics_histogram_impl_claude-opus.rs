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
proof fn lemma_sum_seq_push(s: Seq<usize>, x: usize)
    ensures
        sum_seq(s.push(x)) == sum_seq(s) + x,
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.push(x) =~= seq![x]);
        assert(sum_seq(s.push(x)) == x);
        assert(sum_seq(s) == 0);
    } else {
        assert(s.push(x).drop_first() =~= s.drop_first().push(x));
        lemma_sum_seq_push(s.drop_first(), x);
    }
}

/* helper modified by LLM (iteration 4): preserving type signature fix */
proof fn lemma_sum_seq_update(s: Seq<usize>, idx: int, val: usize)
    requires
        0 <= idx < s.len(),
    ensures
        sum_seq(s.update(idx, val)) == sum_seq(s) - s[idx] + val,
    decreases s.len()
{
    if idx == 0 {
        assert(s.update(0, val).drop_first() =~= s.drop_first());
    } else {
        assert(s.update(idx, val).drop_first() =~= s.drop_first().update(idx - 1, val));
        lemma_sum_seq_update(s.drop_first(), idx - 1, val);
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
    /* code modified by LLM (iteration 4): moved view operation inside proof block */
    let bin_width = ((max_val - min_val) as usize) / n_bins;
    let mut edges = Vec::new();
    let mut counts = Vec::new();
    
    let mut i: usize = 0;
    while i <= n_bins
        invariant
            edges.len() == i,
            i <= n_bins,
            forall|j: int| 0 <= j && j < i ==> edges@[j] == min_val + (j * bin_width) as i8,
    {
        edges.push(min_val + (i * bin_width) as i8);
        i = i + 1;
    }
    
    if n_bins > 0 {
        edges.set(n_bins, max_val);
    }
    
    i = 0;
    while i < n_bins
        invariant
            counts.len() == i,
            i <= n_bins,
            edges.len() == n_bins + 1,
            edges[0] == min_val,
            edges[n_bins as int] == max_val,
    {
        counts.push(0);
        i = i + 1;
    }
    
    i = 0;
    while i < data.len()
        invariant
            i <= data.len(),
            counts.len() == n_bins,
            edges.len() == n_bins + 1,
            edges[0] == min_val,
            edges[n_bins as int] == max_val,
            sum_seq(counts@) == data@.take(i as int).filter(|x: i8| (min_val as int) <= (x as int) && (x as int) <= (max_val as int)).len(),
    {
        let val = data[i];
        if min_val <= val && val <= max_val {
            let mut bin_idx = 0;
            while bin_idx < n_bins - 1
                invariant
                    bin_idx < n_bins,
                    counts.len() == n_bins,
            {
                if val < edges[bin_idx + 1] {
                    break;
                }
                bin_idx = bin_idx + 1;
            }
            let old_count = counts[bin_idx];
            let new_count: usize = old_count + 1;
            counts.set(bin_idx, new_count);
            proof {
                let old_counts = counts@;
                lemma_sum_seq_update(old_counts, bin_idx as int, new_count);
                assert(sum_seq(counts@) == sum_seq(old_counts) + 1);
            }
        }
        i = i + 1;
    }
    
    assert(data@.take(data.len() as int) =~= data@);
    (counts, edges)
}
// </vc-code>

}
fn main() {}