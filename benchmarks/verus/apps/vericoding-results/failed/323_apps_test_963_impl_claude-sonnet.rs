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
/* helper modified by LLM (iteration 5): Added safe modular conversion helper function */
fn safe_mod_convert(x: i32) -> (result: i8)
    requires x >= 0, x < 998244353
    ensures result == (x % 998244353) as i8
{
    (x % 998244353) as i8
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
    /* code modified by LLM (iteration 5): Fixed cast attribute placement and removed unverified truncate */
    let mut dp = Vec::new();
    let mut prefix_sum = Vec::new();
    
    let mut i = 0i8;
    while i < n + 1
        invariant
            dp.len() == i as usize,
            prefix_sum.len() == i as usize,
            0 <= i <= n + 1
        decreases n + 1 - i
    {
        dp.push(0i32);
        prefix_sum.push(0i32);
        i = i + 1;
    }
    
    dp[1] = 1;
    prefix_sum[1] = 1;
    
    let mut pos = 2i8;
    while pos <= n
        invariant
            dp.len() == (n + 1) as usize,
            prefix_sum.len() == (n + 1) as usize,
            2 <= pos <= n + 1,
            dp[1] == 1,
            prefix_sum[1] == 1
        decreases n - pos + 1
    {
        let mut seg_contributions = 0i32;
        let mut seg_index = 0i8;
        
        while seg_index < k
            invariant
                0 <= seg_index <= k,
                seg_contributions >= 0,
                seg_contributions < 998244353,
                dp.len() == (n + 1) as usize,
                segments.len() == k as usize
            decreases k - seg_index
        {
            let start = segments[seg_index as usize].0;
            let end = segments[seg_index as usize].1;
            let i_s = if pos >= start { pos - start } else { 0 };
            let i_e = if pos > end { pos - end - 1 } else { 0 };
            
            let contribution = (prefix_sum[i_s as usize] - prefix_sum[i_e as usize] + 998244353) % 998244353;
            seg_contributions = (seg_contributions + contribution) % 998244353;
            seg_index = seg_index + 1;
        }
        
        dp[pos as usize] = seg_contributions;
        if pos > 1 {
            prefix_sum[pos as usize] = (prefix_sum[(pos - 1) as usize] + seg_contributions) % 998244353;
        }
        pos = pos + 1;
    }
    
    let final_result = dp[n as usize] % 998244353;
    safe_mod_convert(final_result)
}
// </vc-code>


}

fn main() {}