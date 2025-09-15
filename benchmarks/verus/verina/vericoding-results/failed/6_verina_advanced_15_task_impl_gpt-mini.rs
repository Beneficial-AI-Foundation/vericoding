// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_index(i: int, n: int) -> bool { 0 <= i && i < n }
// </vc-helpers>

// <vc-spec>
fn increasing_triplet(nums: &Vec<i32>) -> (result: bool)
    ensures
        result ==> exists|i: int, j: int, k: int| 
            0 <= i < j && j < k < nums.len() && 
            nums[i] < nums[j] && nums[j] < nums[k],
        !result ==> forall|i: int, j: int, k: int| 
            0 <= i < j && j < k < nums.len() ==> 
            !(nums[i] < nums[j] && nums[j] < nums[k]),
// </vc-spec>
// <vc-code>
{
    let n = nums.len();
    if n < 3 {
        proof {
            assert(forall|ii:int, jj:int, kk:int| 0 <= ii < jj && jj < kk && kk < n ==> !(nums@[ii] < nums@[jj] && nums@[jj] < nums@[kk]));
        }
        return false;
    }
    let mut i: int = 0;
    while i <= n - 3
        invariant 0 <= i && i <= n
        invariant forall|ii:int, jj:int, kk:int| 0 <= ii < jj && jj < kk && kk < n && ii < i ==> !(nums@[ii] < nums@[jj] && nums@[jj] < nums@[kk])
        decreases n - i
    {
        let mut j: int = i + 1;
        while j <= n - 2
            invariant i + 1 <= j && j <= n
            invariant forall|jj:int, kk:int| 0 <= jj < kk && kk < n && i < jj && jj < j ==> !(nums@[i] < nums@[jj] && nums@[jj] < nums@[kk])
            decreases n - j
        {
            let mut k: int = j + 1;
            while k <= n - 1
                invariant j + 1 <= k && k <= n
                invariant forall|kk:int| 0 <= kk && kk < n && j < kk && kk < k ==> !(nums@[i] < nums@[j] && nums@[j] < nums@[kk])
                decreases n - k
            {
                if nums@[i] < nums@[j] && nums@[j] < nums@[k] {
                    proof {
                        assert(0 <= i && i < j && j < k && k < n);
                        assert(nums@[i] < nums@[j] && nums@[j] < nums@[k]);
                        assert(exists|ii:int, jj:int, kk:int| 0 <= ii < jj && jj < kk && kk < n && nums@[ii] < nums@[jj] && nums@[jj] < nums@[kk]);
                    }
                    return true;
                }
                k = k + 1;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    proof {
        assert(forall|ii:int, jj:int, kk:int| 0 <= ii < jj && jj < kk && kk < n ==> !(nums@[ii] < nums@[jj] && nums@[jj] < nums@[kk]));
    }
    return false;
}
// </vc-code>

}
fn main() {}