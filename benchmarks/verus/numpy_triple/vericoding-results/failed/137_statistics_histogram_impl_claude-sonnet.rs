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
/* helper modified by LLM (iteration 5): fixed arithmetic overflow and bounds checking */
fn bins_for_histogram(n_bins: usize, min_val: i32, max_val: i32) -> (result: Vec<i32>)
    requires n_bins > 0, min_val < max_val
    ensures result.len() == n_bins + 1, result[0] == min_val, result[n_bins as int] == max_val
{
    let mut bins = Vec::new();
    let range = (max_val as i64) - (min_val as i64);
    let mut i = 0;
    while i <= n_bins
        invariant 0 <= i <= n_bins + 1, bins.len() == i, i > 0 ==> bins[0] == min_val, i > n_bins ==> bins[n_bins as int] == max_val
        decreases n_bins + 1 - i
    {
        if i == 0 {
            bins.push(min_val);
        } else if i == n_bins {
            bins.push(max_val);
        } else {
            let bin_val = min_val + ((range * i as i64) / n_bins as i64) as i32;
            bins.push(bin_val);
        }
        i += 1;
    }
    bins
}

fn count_in_range(data: &Vec<i32>, min_val: i32, max_val: i32) -> (result: usize)
    ensures result == data@.filter(|x: i32| min_val <= x && x <= max_val).len()
{
    let mut count = 0;
    let mut i = 0;
    while i < data.len()
        invariant 0 <= i <= data.len(), count == data@.take(i as int).filter(|x: i32| min_val <= x && x <= max_val).len()
        decreases data.len() - i
    {
        if min_val <= data[i] && data[i] <= max_val {
            count += 1;
        }
        i += 1;
    }
    count
}

proof fn sum_seq_append_zero(s: Seq<usize>)
    ensures sum_seq(s.push(0)) == sum_seq(s)
{
    if s.len() == 0 {
        assert(sum_seq(s.push(0)) == 0 + sum_seq(seq![]));
    } else {
        sum_seq_append_zero(s.drop_first());
    }
}

proof fn sum_seq_increment_last(s: Seq<usize>, idx: int)
    requires 0 <= idx < s.len()
    ensures sum_seq(s.update(idx, s[idx] + 1)) == sum_seq(s) + 1
{
    if idx == 0 {
        assert(sum_seq(s.update(0, s[0] + 1)) == (s[0] + 1) + sum_seq(s.drop_first()));
    } else {
        sum_seq_increment_last(s.drop_first(), idx - 1);
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
{
    /* code modified by LLM (iteration 5): fixed precondition and invariant errors */
    let bins = bins_for_histogram(n_bins, min_val, max_val);
    let mut counts = Vec::new();
    let mut i = 0;
    while i < n_bins
        invariant 0 <= i <= n_bins, counts.len() == i
        decreases n_bins - i
    {
        counts.push(0);
        i += 1;
    }
    
    proof {
        sum_seq_append_zero(seq![]);
        assert(sum_seq(counts@) == 0);
        assert(data@.take(0).filter(|x: i32| min_val <= x && x <= max_val).len() == 0);
    }
    
    let mut j = 0;
    while j < data.len()
        invariant 
            0 <= j <= data.len(), 
            counts.len() == n_bins,
            sum_seq(counts@) == data@.take(j as int).filter(|x: i32| min_val <= x && x <= max_val).len()
        decreases data.len() - j
    {
        if min_val <= data[j] && data[j] <= max_val {
            let mut bin_idx = 0;
            if data[j] == max_val {
                bin_idx = n_bins - 1;
            } else {
                let range = (max_val as i64) - (min_val as i64);
                let normalized = (data[j] as i64) - (min_val as i64);
                let calc_idx = (normalized * n_bins as i64) / range;
                bin_idx = if calc_idx >= n_bins as i64 { n_bins - 1 } else { calc_idx as usize };
            }
            proof {
                sum_seq_increment_last(counts@, bin_idx as int);
            }
            counts.set(bin_idx, counts[bin_idx] + 1);
        }
        j += 1;
    }
    
    (counts, bins)
}
// </vc-code>

}
fn main() {}