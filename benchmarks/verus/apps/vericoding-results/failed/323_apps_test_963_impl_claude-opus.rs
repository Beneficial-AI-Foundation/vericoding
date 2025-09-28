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
    /* code modified by LLM (iteration 3): added decreases clauses to all loops */
    let mut dp: Vec<i8> = Vec::new();
    let mut prefix_sum: Vec<i8> = Vec::new();
    
    // Initialize vectors with zeros
    let mut i: usize = 0;
    while i <= n as usize
        invariant
            i <= n as usize + 1,
            dp.len() == i,
            prefix_sum.len() == i,
            forall|j: int| 0 <= j < i ==> dp[j] == 0,
            forall|j: int| 0 <= j < i ==> prefix_sum[j] == 0,
        decreases n as usize + 1 - i
    {
        dp.push(0);
        prefix_sum.push(0);
        i = i + 1;
    }
    
    // Set initial values
    dp.set(1, 1);
    prefix_sum.set(1, 1);
    
    let mut pos: usize = 2;
    while pos <= n as usize
        invariant
            2 <= pos <= n as usize + 1,
            dp.len() == (n + 1) as usize,
            prefix_sum.len() == (n + 1) as usize,
            dp[1] == 1,
            prefix_sum[1] == 1,
        decreases n as usize + 1 - pos
    {
        let mut seg_index: usize = 0;
        let mut acc: i8 = 0;
        
        while seg_index < k as usize
            invariant
                seg_index <= k as usize,
                acc < 998244353,
            decreases k as usize - seg_index
        {
            let start = segments[seg_index].0;
            let end = segments[seg_index].1;
            let i_s = if pos as i8 - start >= 0 { (pos as i8 - start) as usize } else { 0 };
            let i_e = if pos as i8 - end - 1 >= 0 { (pos as i8 - end - 1) as usize } else { 0 };
            let contribution = ((prefix_sum[i_s] as i32 - prefix_sum[i_e] as i32 + 998244353) % 998244353) as i8;
            acc = ((acc as i32 + contribution as i32) % 998244353) as i8;
            seg_index = seg_index + 1;
        }
        
        dp.set(pos, acc);
        prefix_sum.set(pos, ((prefix_sum[pos - 1] as i32 + dp[pos] as i32) % 998244353) as i8);
        pos = pos + 1;
    }
    
    dp[n as usize]
}
// </vc-code>


}

fn main() {}