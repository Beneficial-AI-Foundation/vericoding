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
/* helper modified by LLM (iteration 5): lemma to relate int bounds to usize casting */
fn lemma_int_le_to_usize(x: int, n: int)
    requires
        0 <= x,
        x <= n,
    ensures
        x as usize <= n as usize,
{
    proof {
        assert(0 <= x);
        assert(x <= n);
    }
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
    /* code modified by LLM (iteration 5): implement DP with bounds invariants and proofs tying spec-level segments to runtime vector */
    let MOD: i64 = 998244353;
    let nn: i64 = n as i64;

    let size: usize = (nn + 1) as usize;
    let mut dp: Vec<i64> = Vec::new();
    let mut prefix: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < size
        invariant
            i <= size,
            dp.len() == i,
            prefix.len() == i,
        decreases size - i
    {
        if i == 1 {
            dp.push(1);
            prefix.push(1);
        } else {
            dp.push(0);
            prefix.push(0);
        }
        i += 1;
    }

    proof {
        assert(segments@.len() == segments.len() as int);
        assert(segments@.len() == k as int);
    }

    let mut pos: i64 = 2;
    while pos <= nn
        invariant
            2 <= pos <= nn,
            pos as usize < size,
            dp.len() == size,
            prefix.len() == size,
        decreases nn - pos + 1
    {
        let mut new_dp_val: i64 = 0;
        let mut sidx: usize = 0;
        while sidx < segments.len()
            invariant
                sidx <= segments.len(),
                dp.len() == size,
                prefix.len() == size,
            decreases segments.len() - sidx
        {
            let (st_i8, en_i8) = segments[sidx];
            let st: i64 = st_i8 as i64;
            let en: i64 = en_i8 as i64;
            proof {
                let j_int: int = sidx as int;
                assert(0 <= j_int && j_int < segments@.len());
                assert(segments@[j_int].0 >= 1 && segments@[j_int].1 <= n as int && segments@[j_int].0 <= segments@[j_int].1);
                assert(st as int == segments@[j_int].0);
                assert(en as int == segments@[j_int].1);
            }
            let i_s = if st <= pos { (pos - st) as usize } else { 0usize };
            let i_e = if en + 1 <= pos { (pos - (en + 1)) as usize } else { 0usize };
            let contribution = (prefix[i_s] - prefix[i_e] + MOD) % MOD;
            new_dp_val = (new_dp_val + contribution) % MOD;
            sidx += 1;
        }
        let pos_usize: usize = pos as usize;
        dp[pos_usize] = new_dp_val;
        let prev_usize: usize = (pos - 1) as usize;
        prefix[pos_usize] = (prefix[prev_usize] + new_dp_val) % MOD;
        pos = pos + 1;
    }

    let result_val: i64 = dp[nn as usize];
    result_val as i8
}

// </vc-code>


}

fn main() {}