// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): adopted from previous version */
spec fn is_strictly_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j]
}
// </vc-helpers>

// <vc-spec>
fn longest_increasing_subsequence(nums: &Vec<i32>) -> (result: i32)
    ensures
        result >= 0,
        result <= nums.len() as i32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed compilation errors by accessing Ghost values directly */
    let n = nums.len();
    if n == 0 {
        return 0i32;
    }
    let mut tails: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            tails.len() <= i,
            is_strictly_sorted(tails.view()),
        decreases n - i
    {
        let num = nums[i];

        let mut lo: usize = 0;
        let mut hi: usize = tails.len();
        
        let tails_snapshot = Ghost(tails.view());

        while lo < hi
            invariant
                0 <= lo <= hi <= tails.len(),
                tails.view() == tails_snapshot,
                is_strictly_sorted(tails.view()),
                forall|k: int| 0 <= k < lo ==> tails.view().index(k) < num,
                forall|k: int| hi <= k < tails.len() ==> tails.view().index(k) >= num,
            decreases hi - lo
        {
            let mid = lo + (hi - lo) / 2;
            if tails[mid] < num {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        if lo == tails.len() {
            let old_tails = Ghost(tails.view());
            tails.push(num);
            proof {
                assert(forall|k: int| 0 <= k < old_tails.len() ==> old_tails[k] < num);
            }
        } else {
            let old_tails = Ghost(tails.view());
            tails.set(lo, num);
            proof {
                let s = old_tails;
                assert(is_strictly_sorted(s));
                assert(lo > 0 ==> s[lo as int - 1] < num);
                assert(num <= s[lo as int]);
                if lo < s.len() - 1 {
                    assert(s[lo as int] < s[lo as int + 1]);
                    assert(num < s[lo as int + 1]);
                }
            }
        }
        
        i += 1;
    }

    tails.len() as i32
}
// </vc-code>

}
fn main() {}