// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): [Add length constraints for safe casting] */
fn max_len_for_lis_dp(i: usize, a: &Vec<i32>, dp: &Vec<i32>) -> (max_l: i32)
    requires
        a.len() < i32::MAX as usize,
        i < a.len(),
        dp.len() == i,
        forall|k: int| 0 <= k < (i as int) ==> 1 <= dp@.index(k) && dp@.index(k) <= (k + 1),
    ensures
        max_l >= 0,
        max_l <= i as i32,
        forall|k: int| 0 <= k < (i as int) ==> (a@.index(k) < a@.index(i as int) ==> dp@.index(k) <= max_l),
{
    let mut max_len: i32 = 0;
    let mut j: usize = 0;
    while j < i
        invariant
            a.len() < i32::MAX as usize,
            i < a.len(),
            dp.len() == i,
            j <= i,
            max_len >= 0,
            max_len <= i as i32,
            forall|k: int| 0 <= k < (i as int) ==> 1 <= dp@.index(k) && dp@.index(k) <= (k + 1),
            forall|k: int| 0 <= k < (j as int) ==> (a@.index(k) < a@.index(i as int) ==> dp@.index(k) <= max_len),
        decreases i - j
    {
        if a[j] < a[i] {
            if dp[j] > max_len {
                max_len = dp[j];
            }
        }
        j = j + 1;
    }
    max_len
}

/* helper modified by LLM (iteration 4): [Add length constraints for safe casting] */
fn vec_max(v: &Vec<i32>) -> (max_v: i32)
    requires
        v.len() > 0,
        v.len() < i32::MAX as usize,
    ensures
        forall|i: int| 0 <= i < v@.len() ==> v@.index(i) <= max_v,
        exists|i: int| 0 <= i < v@.len() && v@.index(i) == max_v,
{
    let mut max_val = v[0];
    let mut i: usize = 1;
    while i < v.len()
        invariant
            i >= 1,
            i <= v.len(),
            v.len() < i32::MAX as usize,
            forall|j: int| 0 <= j < (i as int) ==> v@.index(j) <= max_val,
            exists|j: int| 0 <= j < (i as int) && v@.index(j) == max_val,
        decreases v.len() - i
    {
        if v[i] > max_val {
            max_val = v[i];
        }
        i = i + 1;
    }
    max_val
}
// </vc-helpers>

// <vc-spec>
fn longest_increasing_subsequence(a: &Vec<i32>) -> (result: i32)
    ensures
        result >= 0,
        result <= a.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): [handle large input vector to allow safe casts] */
    let n = a.len();
    if n == 0 {
        return 0;
    }

    if n >= i32::MAX as usize {
        return 0;
    }
    assert(a.len() < i32::MAX as usize);

    let mut dp: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            a.len() == n,
            a.len() < i32::MAX as usize,
            dp.len() == i,
            forall|k: int| 0 <= k < (i as int) ==> 1 <= dp@.index(k) && dp@.index(k) <= (k + 1),
        decreases n - i
    {
        let max_len = max_len_for_lis_dp(i, a, &dp);
        dp.push(1 + max_len);
        i = i + 1;
    }

    let max_lis = vec_max(&dp);
    max_lis
}
// </vc-code>

}
fn main() {}