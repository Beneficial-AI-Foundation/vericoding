// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): construct increasing triple from mid */
fn triple_from_mid(nums: &Vec<i32>, p: int, j: int, i: int)
    requires
        0 <= p && p < j && j < i && i < nums.len() as int,
        nums[p] < nums[j],
        nums[j] < nums[i],
    ensures
        exists|a: int, b: int, c: int|
            0 <= a && a < b && b < c && c < nums.len() as int && nums[a] < nums[b] && nums[b] < nums[c],
{
    proof {
        exists|a: int, b: int, c: int|
            a == p && b == j && c == i && 0 <= a && a < b && b < c && c < nums.len() as int && nums[a] < nums[b] && nums[b] < nums[c];
    }
}
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
/* code modified by LLM (iteration 5): find increasing triplet using two-pointer tracking with int indices */
{
    let INF: i32 = 2147483647;
    let mut i: int = 0;
    let mut small: i32 = INF;
    let mut small_idx: int = nums.len() as int;
    let mut mid: i32 = INF;
    let mut mid_idx: int = nums.len() as int;
    let mut mid_prev: int = nums.len() as int;

    if nums.len() < 3 {
        return false;
    }

    while i < nums.len() as int
        invariant
            0 <= i,
            i <= nums.len() as int,
            forall|a: int, b: int, c: int| 0 <= a && a < b && b < c && c < i ==> !(nums[a] < nums[b] && nums[b] < nums[c]),
            forall|k: int| 0 <= k && k < i ==> nums[k] >= small,
            (small_idx == nums.len() as int) ==> small == INF,
            (small_idx != nums.len() as int) ==> 0 <= small_idx && small_idx < i && nums[small_idx] == small,
            forall|a: int, b: int| 0 <= a && a < b && b < i ==> nums[b] >= mid,
            (mid_idx == nums.len() as int) ==> mid == INF,
            (mid_idx != nums.len() as int) ==> 0 <= mid_prev && mid_prev < mid_idx && mid_idx < i && nums[mid_idx] == mid && nums[mid_prev] < nums[mid],
        decreases
            nums.len() as int - i
    {
        let x: i32 = nums[i as usize];
        if x <= small {
            small = x;
            small_idx = i;
            i = i + 1;
        } else if x <= mid {
            assert(small_idx != nums.len() as int);
            let s: int = small_idx;
            mid = x;
            mid_idx = i;
            mid_prev = s;
            i = i + 1;
        } else {
            assert(mid_idx != nums.len() as int);
            let mp: int = mid_prev;
            let mi: int = mid_idx;
            triple_from_mid(nums, mp, mi, i);
            return true;
        }
    }

    return false;
}

// </vc-code>

}
fn main() {}