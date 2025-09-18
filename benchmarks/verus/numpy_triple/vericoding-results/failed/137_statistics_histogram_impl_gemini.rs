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
/* helper modified by LLM (iteration 5): no logical changes */
proof fn lemma_sum_increment(s: Seq<usize>, i: int)
    requires 0 <= i < s.len()
    ensures sum_seq(s.update(i, s[i] + 1)) == sum_seq(s) + 1
    decreases s.len() - i
{
    reveal(sum_seq);
    if i == 0 {
        assert(s.update(i, s[i] + 1).drop_first() =~= s.drop_first());
    } else {
        assert(s.drop_first().update(i - 1, s.drop_first()[(i - 1) as int] + 1)
            =~= s.update(i, s[i] + 1).drop_first());
        lemma_sum_increment(s.drop_first(), i - 1);
    }
}

/* helper modified by LLM (iteration 5): no logical changes */
proof fn lemma_sum_of_zeros(len: nat)
    ensures sum_seq(Seq::new(len, |i: int| 0usize)) == 0
    decreases len
{
    reveal(sum_seq);
    let s = Seq::new(len, |i: int| 0usize);
    if len > 0 {
        assert(s.drop_first() =~= Seq::new(len - 1, |i: int| 0usize));
        lemma_sum_of_zeros(len - 1);
    }
}

/* helper modified by LLM (iteration 5): no logical changes */
proof fn lemma_bin_index_in_range(x: i32, min_val: i32, max_val: i32, n_bins: usize)
    requires
        n_bins > 0,
        min_val < max_val,
        min_val <= x < max_val,
    ensures
        0 <= ((x - min_val) * (n_bins as i32)) / (max_val - min_val) < (n_bins as i32),
{
    let range = max_val - min_val;
    let n_bins_i32 = n_bins as i32;
    vstd::arithmetic::div_mod::lemma_div_is_ordered(x - min_val, range, n_bins_i32);
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
/* code modified by LLM (iteration 5): fixed compilation errors from incorrect vstd function calls */
{
    let mut bin_edges: Vec<i32> = Vec::with_capacity((n_bins + 1) as usize);
    let range = max_val - min_val;
    let n_bins_i32 = n_bins as i32;

    let mut i: usize = 0;
    while i <= n_bins
        invariant
            i <= n_bins + 1,
            bin_edges.len() == i,
            bin_edges.capacity() >= n_bins + 1,
            range == max_val - min_val,
            n_bins_i32 == n_bins as i32,
            n_bins > 0,
            forall|j: int| 0 <= j < i ==> bin_edges@[j] == min_val + (j as i32 * range) / n_bins_i32,
    {
        bin_edges.push(min_val + (i as i32 * range) / n_bins_i32);
        i += 1;
    }

    proof {
        vstd::arithmetic::div_mod::lemma_mul_div_cancel(range, n_bins_i32);
    }
    assert(bin_edges@[0] == min_val);
    assert(bin_edges@[n_bins as int] == max_val);

    let mut counts = vec![0; n_bins];
    proof {
        lemma_sum_of_zeros(n_bins as nat);
    }

    let mut data_idx = 0;
    while data_idx < data.len()
        invariant
            data_idx <= data.len(),
            counts.len() == n_bins,
            bin_edges.len() == n_bins + 1,
            range == max_val - min_val,
            n_bins_i32 == n_bins as i32,
            n_bins > 0,
            min_val < max_val,
            sum_seq(counts@) == data@.take(data_idx as int).filter(|x: i32| min_val <= x && x <= max_val).len(),
    {
        let x = data[data_idx];
        let old_counts = old(counts)@;

        if min_val <= x && x <= max_val {
            let bin_index = if x == max_val {
                n_bins - 1
            } else {
                proof {
                    lemma_bin_index_in_range(x, min_val, max_val, n_bins);
                }
                (((x - min_val) * n_bins_i32) / range) as usize
            };

            assert(0 <= bin_index < n_bins);
            counts.set(bin_index, counts[bin_index] + 1);
            
            proof {
                lemma_sum_increment(old_counts, bin_index as int);
                let s = data@.take(data_idx as int);
                let p = |y: i32| min_val <= y && y <= max_val;
                vstd::seq_lib::lemma_filter_push(s, x, p);
            }
        } else {
            proof {
                assert(sum_seq(counts@) == sum_seq(old_counts));
                let s = data@.take(data_idx as int);
                let p = |y: i32| min_val <= y && y <= max_val;
                vstd::seq_lib::lemma_filter_push(s, x, p);
            }
        }

        data_idx += 1;
    }

    (counts, bin_edges)
}
// </vc-code>

}
fn main() {}