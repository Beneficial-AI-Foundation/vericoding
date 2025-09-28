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

proof fn lemma_mod_arithmetic(a: int, b: int, m: int)
    requires m > 0,
    ensures (a % m + b % m) % m == (a + b) % m,
{
}

proof fn lemma_valid_input_properties(n: int, k: int, segments: Seq<(int, int)>)
    requires valid_input(n, k, segments),
    ensures forall|i: int| 0 <= i < k ==> segments[i].0 >= 1 && segments[i].1 <= n && segments[i].0 <= segments[i].1,
    ensures forall|i: int, j: int| 0 <= i < j < k ==> segments[i].1 < segments[j].0 || segments[j].1 < segments[i].0,
{
}

spec fn ensure_positive_mod(x: int, m: int) -> int
    requires m > 0,
    ensures 0 <= result < m,
{
    (x % m + m) % m
}

spec fn convert_i8_to_int(x: i8) -> int {
    x as int
}

spec fn convert_vec_to_seq(vec: Vec<(i8, i8)>) -> Seq<(int, int)> {
    vec@.map(|idx, seg: (i8, i8)| (seg.0 as int, seg.1 as int))
}

proof fn lemma_i8_conversion_valid()
    ensures forall|x: i8| convert_i8_to_int(x) >= -128 && convert_i8_to_int(x) <= 127,
{
}

/* helper modified by LLM (iteration 5): Fixed valid_input spec syntax */
spec fn valid_input_fixed(n: int, k: int, segments: Seq<(int, int)>) -> bool {
    n >= 2 &&
    k >= 1 &&
    segments.len() == k &&
    (forall|i: int| 0 <= i < k ==> segments[i].0 >= 1 && segments[i].1 <= n && segments[i].0 <= segments[i].1) &&
    (forall|i: int, j: int| 0 <= i < j < k ==> segments[i].1 < segments[j].0 || segments[j].1 < segments[i].0)
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
    /* code modified by LLM (iteration 5): Fixed compilation error and implementation */
    let n_int = n as i32;
    let k_int = k as i32;
    let mut dp: Vec<i32> = Vec::new();
    let mut prefix_sum: Vec<i32> = Vec::new();
    
    dp.resize((n_int + 1) as usize, 0);
    prefix_sum.resize((n_int + 1) as usize, 0);
    
    dp[1] = 1;
    prefix_sum[1] = 1;
    
    for pos in 2..=n_int {
        let mut total_contribution: i32 = 0;
        
        for seg_index in 0..k_int {
            let segment = segments[seg_index as usize];
            let start = segment.0 as i32;
            let end = segment.1 as i32;
            let pos_i32 = pos as i32;
            
            let i_s = if pos_i32 - start >= 0 { (pos_i32 - start) as usize } else { 0 };
            let i_e = if pos_i32 - end - 1 >= 0 { (pos_i32 - end - 1) as usize } else { 0 };
            
            let contribution = (prefix_sum[i_s] - prefix_sum[i_e] + 998244353) % 998244353;
            total_contribution = (total_contribution + contribution) % 998244353;
        }
        
        dp[pos as usize] = total_contribution;
        prefix_sum[pos as usize] = (prefix_sum[(pos - 1) as usize] + total_contribution) % 998244353;
    }
    
    (dp[n_int as usize] % 256) as i8
}
// </vc-code>


}

fn main() {}