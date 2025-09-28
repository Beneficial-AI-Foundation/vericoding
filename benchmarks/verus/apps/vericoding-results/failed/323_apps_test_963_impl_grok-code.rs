// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int, segments: Seq<(int, int)>) -> bool {
    n >= 2 &&
    k >= 1 &&
    segments.len() == k &&
    (forall|i: int| 0 <= i < k ==> segments[i].0 >= 1 && segments[i].1 <= n && segments[i].0 <= segments[i].1) &&
    (forall|i: int, j: int| 0 <= i < j < k ==> segments[i].1 < segments[j].0 || segments[j].1 < segments[i].0)
}

spec fn compute_ways_dp(n: int, k: int, segments: Seq<(int, int)>) -> int {
    let dp = Map::new(|i: int| 0 <= i <= n, |i: int| if i == 1 { 1 } else { 0 });
    let prefix_sum = Map::new(|i: int| 0 <= i <= n, |i: int| if i == 1 { 1 } else { 0 });
    compute_ways_dp_helper(n, k, segments, dp, prefix_sum, 2)
}

spec fn compute_ways_dp_helper(n: int, k: int, segments: Seq<(int, int)>, dp: Map<int, int>, prefix_sum: Map<int, int>, pos: int) -> int
    decreases n - pos + 1
{
    if pos > n {
        dp[n] % 998244353
    } else {
        let new_dp_val = compute_segment_contributions(pos, k, segments, prefix_sum, 0, 0);
        let new_prefix_sum_val = (prefix_sum[pos-1] + new_dp_val) % 998244353;
        let updated_dp = dp.insert(pos, new_dp_val);
        let updated_prefix_sum = prefix_sum.insert(pos, new_prefix_sum_val);
        compute_ways_dp_helper(n, k, segments, updated_dp, updated_prefix_sum, pos + 1)
    }
}

spec fn compute_segment_contributions(pos: int, k: int, segments: Seq<(int, int)>, prefix_sum: Map<int, int>, seg_index: int, acc: int) -> int
    decreases k - seg_index
{
    if seg_index >= k {
        acc
    } else {
        let start = segments[seg_index].0;
        let end = segments[seg_index].1;
        let i_s = if pos - start >= 0 { pos - start } else { 0 };
        let i_e = if pos - end - 1 >= 0 { pos - end - 1 } else { 0 };
        let contribution = (prefix_sum[i_s] - prefix_sum[i_e] + 998244353) % 998244353;
        let new_acc = (acc + contribution) % 998244353;
        compute_segment_contributions(pos, k, segments, prefix_sum, seg_index + 1, new_acc)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, segments: Vec<(i8, i8)>) -> (result: i8)
    requires 
        valid_input(n as int, k as int, segments@.map(|idx, seg: (i8, i8)| (seg.0 as int, seg.1 as int)))
    ensures 
        result < 998244353 &&
        result == compute_ways_dp(n as int, k as int, segments@.map(|idx, seg: (i8, i8)| (seg.0 as int, seg.1 as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type casts for indexing sequences and vectors, corrected modulo arithmetic operators and casts, adjusted variable types for indexing. */
    let MOD: u32 = 998244353;
    let n_i = n as usize;
    let k_i = k as usize;
    let mut dp = Vec::<u32>::new();
    let mut prefix_sum = Vec::<u32>::new();
    let mut i = 0usize;
    while i <= n_i {
        dp.push(0);
        prefix_sum.push(0);
        i += 1;
    }
    dp[1] = 1;
    prefix_sum[1] = 1;
    let ghost mut dp_spec: Map<int, int> = Map::empty();
    let ghost mut prefix_spec: Map<int, int> = Map::empty();
    proof {
        dp_spec = dp_spec.insert(1, 1);
        prefix_spec = prefix_spec.insert(1, 1);
    }
    let mut pos = 2usize;
    while pos <= n_i
        invariant
            2 <= pos <= n_i + 1,
            dp@.len() == n_i + 1,
            prefix_sum@.len() == n_i + 1,
            dp_spec.dom() =~= Set::new(|i: int| 1 <= i < pos as int),
            prefix_spec.dom() =~= Set::new(|i: int| 1 <= i < pos as int),
            forall|i: int| 1 <= i < pos as int ==> dp@[i] as int == dp_spec[i],
            forall|i: int| 1 <= i < pos as int ==> prefix_sum@[i] as int == prefix_spec[i],
        decreases n_i - pos + 1
    {
        let mut acc = 0u32;
        let ghost mut acc_spec: int = 0;
        let mut seg_index = 0usize;
        while seg_index < k_i
            invariant
                seg_index <= k_i,
                acc as int == acc_spec,
            decreases k_i - seg_index
        {
            let start = segments[seg_index].0 as usize;
            let end = segments[seg_index].1 as usize;
            let i_s_usize = if pos > start { pos - start } else { 0 };
            let i_e_usize = if pos > end + 1 { pos - end - 1 } else { 0 };
            let prefix_at_i_s = if i_s_usize > 0 { prefix_sum[i_s_usize] } else { 0 };
            let prefix_at_i_e = if i_e_usize > 0 { prefix_sum[i_e_usize] } else { 0 };
            let contribution_u64 = ((((prefix_at_i_s as u64) + (MOD as u64)) - prefix_at_i_e as u64) % (MOD as u64));
            let contribution = contribution_u64 as u32;
            acc = (((acc as u64 + contribution as u64) % (MOD as u64))) as u32;
            proof {
                let seg_idx = seg_index as int;
                let pos_int = pos as int;
                let start_int = segments@[seg_idx].0;
                let end_int = segments@[seg_idx].1;
                let i_s = if pos_int - start_int >= 0 { pos_int - start_int } else { 0 };
                let i_e = if pos_int - end_int - 1 >= 0 { pos_int - end_int - 1 } else { 0 };
                let spec_contribution = ((prefix_spec[i_s] - prefix_spec[i_e] + (MOD as int)) % (MOD as int));
                acc_spec = (acc_spec + spec_contribution) % (MOD as int);
            }
            seg_index += 1;
        }
        dp[pos] = acc;
        prefix_sum[pos] = ((((prefix_sum[pos - 1] as u64 + acc as u64) % (MOD as u64)))) as u32;
        proof {
            dp_spec = dp_spec.insert(pos as int, acc as int);
            prefix_spec = prefix_spec.insert(pos as int, ((prefix_spec[pos as int - 1] + acc as int) % (MOD as int)));
        }
        pos += 1;
    }
    (dp[n_i] as i8)
}
// </vc-code>


}

fn main() {}