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
/* helper modified by LLM (iteration 5): none */
type DPTable = Vec<i32>;
type PrefixSumTable = Vec<i32>;

const MOD: i32 = 998244353;

fn checked_sub(a: i32, b: i32) -> i32
    ensures
        a >= b ==> checked_sub(a, b) == a - b,
        a < b ==> checked_sub(a, b) == a - b + MOD
{
    if a >= b { a - b } else { a - b + MOD }
}
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
    let n_usize = n as usize;
    let k_usize = k as usize;

    let mut dp: DPTable = vec![0; n_usize + 1];
    let mut prefix_sum: PrefixSumTable = vec![0; n_usize + 1];

    dp[1] = 1;
    prefix_sum[1] = 1;

    // Convert segments to a sequence of (usize, usize) for executable code
    let segments_exec_vec: Vec<(usize, usize)> = segments.iter().map(|seg: &(i8, i8)| (seg.0 as usize, seg.1 as usize)).collect();

    let mut pos_usize = 2;
    while pos_usize <= n_usize
        invariant
            pos_usize <= n_usize + 1,
            dp.len() == n_usize + 1,
            prefix_sum.len() == n_usize + 1,
            // ghost state to relate loop with spec
            // this is commented out since the goal for this turn is to address compilation errors only
            /*
            forall|i: int| 1 <= i < pos_usize ==> #[trigger] dp.inv(i, 
                compute_segment_contributions(i, k as int, segments@.map(|idx, seg: (i8, i8)| (seg.0 as int, seg.1 as int)), 
                ghost_prefix_sum_from_vec(&prefix_sum, i as usize), 0, 0)
            ),
            forall|i: int| 1 <= i < pos_usize ==> #[trigger] prefix_sum.inv(i,
                (ghost_prefix_sum_from_vec(&prefix_sum, (i-1) as usize).at(i-1) + 
                compute_segment_contributions(i, k as int, segments@.map(|idx, seg: (i8, i8)| (seg.0 as int, seg.1 as int)), 
                ghost_prefix_sum_from_vec(&prefix_sum, i as usize), 0, 0)) % MOD as int
            ),
            */
    {
        let mut current_dp_val: i32 = 0;
        let mut seg_index_usize = 0;

        while seg_index_usize < k_usize
            invariant
                seg_index_usize <= k_usize,
                segments_exec_vec.len() == k_usize,
        {
            let sg = segments_exec_vec[seg_index_usize];
            let start = sg.0;
            let end = sg.1;

            if pos_usize >= start {
                let i_s = pos_usize - start;
                let i_e_val = pos_usize as isize - (end as isize) - 1;
                let i_e = if i_e_val >= 0 { i_e_val as usize } else { 0 };

                let contribution = checked_sub(prefix_sum[i_s], prefix_sum[i_e]);
                
                current_dp_val = (current_dp_val + contribution) % MOD;
            }
            seg_index_usize += 1;
        }
        dp[pos_usize] = current_dp_val;
        prefix_sum[pos_usize] = (prefix_sum[pos_usize - 1] + current_dp_val) % MOD;
        pos_usize += 1;
    }

    (dp[n_usize] % MOD) as i8
}
// </vc-code>


}

fn main() {}