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
/* helper modified by LLM (iteration 3): changed Seq<nat> to Seq<usize> to match argument type in vc-code */
#[verifier::spinoff_prover]
proof fn lemma_sum_inc(s: Seq<usize>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        sum_seq(s.update(i, s[i] + 1)) == sum_seq(s) + 1,
    decreases s.len(),
{
    if s.len() > 1 && i > 0 {
        lemma_sum_inc(s.drop_first(), i - 1);
    }
}

/* helper modified by LLM (iteration 2): fixed syntax of spec clauses */
fn find_bin_idx(val: i8, boundaries: &Vec<i8>) -> (j: usize)
    requires
        boundaries.len() > 1,
        ({
            let n_bins = (boundaries.len() - 1) as int;
            n_bins > 0 &&
            boundaries[0] <= val && val <= boundaries[n_bins] &&
            forall |i: int, k: int| 0 <= i < k < boundaries.len() ==> boundaries[i] <= boundaries[k]
        }),
    ensures
        ({
            let n_bins = (boundaries.len() - 1) as int;
            (j as int) < n_bins &&
            boundaries[j as int] <= val &&
            (if val == boundaries[n_bins] {
                j as int == n_bins - 1
            } else {
                val < boundaries[(j as int) + 1]
            })
        })
{
    let n_bins = boundaries.len() - 1;
    if val == boundaries[n_bins] {
        return n_bins - 1;
    }

    let mut i: usize = 0;
    while i < n_bins - 1
        invariant
            0 <= i < n_bins,
            val < boundaries[n_bins],
            boundaries[0] <= val,
            forall |k: int| 0 <= k < i ==> boundaries[k + 1] <= val,
        decreases (n_bins - 1) - i
    {
        if val < boundaries[i + 1] {
            return i;
        }
        i = i + 1;
    }
    return i;
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
    /* code modified by LLM (iteration 3): changed `int` to `i64` in exec code, and provided assertions. */
    let mut hist = Vec::from_elem(0, n_bins);
    let mut boundaries = Vec::new();

    let range = (max_val as i64) - (min_val as i64);

    let mut i: usize = 0;
    while i <= n_bins
        invariant
            i <= n_bins + 1,
            boundaries.len() == i,
            n_bins > 0,
            range == (max_val as int) - (min_val as int),
            forall |j: int, k: int| 0 <= j < k < i ==> boundaries[j] <= boundaries[k],
            forall |j: int| 0 <= j < i ==> 
                boundaries[j] == ((min_val as int) + j * range / (n_bins as int)) as i8,
        decreases (n_bins + 1) - i
    {
        let val_exec = (min_val as i64) + (i as i64) * range / (n_bins as i64);
        proof {
            let val_spec = (min_val as int) + (i as int) * range / (n_bins as int);
            assert(min_val as int <= val_spec <= max_val as int);
            assert(i8::MIN <= val_spec <= i8::MAX);
            assert(val_exec == val_spec);
        }
        boundaries.push(val_exec as i8);
        i = i + 1;
    }

    let mut k: usize = 0;
    while k < data.len()
        invariant
            0 <= k <= data.len(),
            hist.len() == n_bins,
            boundaries.len() == n_bins + 1,
            forall |a: int, b: int| 0 <= a < b < boundaries.len() ==> boundaries[a] <= boundaries[b],
            boundaries[0] == min_val,
            boundaries[n_bins as int] == max_val,
            sum_seq(hist@) == data@.subrange(0, k as int).filter(|x: i8| (min_val as int) <= (x as int) && (x as int) <= (max_val as int)).len()
        decreases data.len() - k
    {
        let val = data[k];
        if min_val <= val && val <= max_val {
            let bin_idx = find_bin_idx(val, &boundaries);
            proof {
                lemma_sum_inc(hist@, bin_idx as int);
            }
            hist.set(bin_idx, hist[bin_idx] + 1);
        }
        k = k + 1;
    }

    (hist, boundaries)
}
// </vc-code>

}
fn main() {}