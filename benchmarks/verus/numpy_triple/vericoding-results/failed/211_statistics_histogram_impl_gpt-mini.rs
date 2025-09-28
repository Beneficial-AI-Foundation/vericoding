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
/* helper modified by LLM (iteration 5): predicate to check if a value is within [min, max] inclusive */
spec fn in_range(x: i8, min: i8, max: i8) -> bool {
    (min as int) <= (x as int) && (x as int) <= (max as int)
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
    /* code modified by LLM (iteration 5): use inline range check in executable code, build bins and counts and maintain sum invariant */
    let mut bins = Vec::<i8>::new();
    let mut counts = Vec::<usize>::new();

    let nb = n_bins;
    let mut i: usize = 0;
    while i < nb
        invariant
            i <= nb,
            bins.len() == i,
            counts.len() == i,
        decreases (nb as nat) - (i as nat)
    {
        bins.push(min_val);
        counts.push(0usize);
        i = i + 1;
    }
    bins.push(max_val);

    let len = data.len();
    let mut j: usize = 0;
    while j < len
        invariant
            j <= len,
            counts.len() == n_bins,
            bins.len() == (n_bins + 1),
            sum_seq(counts@) == data@.take(j as int).filter(|x: i8| in_range(x, min_val, max_val)).len(),
        decreases (len as nat) - (j as nat)
    {
        let x = data[j];
        let inr = (min_val as int) <= (x as int) && (x as int) <= (max_val as int);
        if inr {
            let range = (max_val as i32) - (min_val as i32);
            let numerator = (x as i32) - (min_val as i32);
            let mut bin_idx: usize;
            if numerator == range {
                bin_idx = n_bins - 1;
            } else {
                let prod = (numerator as i64) * (n_bins as i64);
                let denom = range as i64;
                let idx64 = (prod / denom) as i64;
                bin_idx = idx64 as usize;
                if bin_idx >= n_bins {
                    bin_idx = n_bins - 1;
                }
            }
            let cur = counts[bin_idx];
            counts.set(bin_idx, cur + 1);
            proof {
                assert(in_range(x, min_val, max_val));
            }
        }
        j = j + 1;
    }

    (counts, bins)
}
// </vc-code>

}
fn main() {}