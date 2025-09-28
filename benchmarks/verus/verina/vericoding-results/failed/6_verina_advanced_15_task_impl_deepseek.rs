// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix method call syntax with parentheses */
proof fn lemma_seq_window_has_triplet(s: Seq<int>, start: int, end: int) 
    requires
        start <= end <= s.len(),
        forall|i: int, j: int, k: int| start <= i < j < k < end ==> !(s[i] < s[j] && s[j] < s[k]),
    ensures
        forall|i: int, j: int| start <= i < j < end ==> s[i] >= s[j]
{
    if start < end {
        lemma_seq_window_has_triplet(s, start, end - 1);
        assert(forall|i: int, j: int| start <= i < j < end - 1 ==> s[i] >= s[j]);
        assert(forall|i: int| start <= i < end - 1 ==> s[i] >= s[end - 1]);
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
{
    /* code modified by LLM (iteration 5): fix syntax error by adding parentheses around method calls */
    let n = nums.len() as int;
    if n < 3 {
        return false;
    }
    
    let mut min_val = nums[0] as int;
    let mut mid_val_opt: Option<int> = None;
    let mut i = 1;
    
    while i < n
        invariant
            1 <= i <= n,
            forall|j: int| 0 <= j < i ==> min_val <= nums[j as usize] as int,
            mid_val_opt.is_some() ==> exists|k: int| 0 <= k < i && min_val < nums[k as usize] as int && nums[k as usize] as int == mid_val_opt.unwrap(),
            mid_val_opt.is_some() ==> forall|j: int| 0 <= j < i ==> !(min_val < nums[j as usize] as int && nums[j as usize] as int < mid_val_opt.unwrap() || false),
        decreases n - i
    {
        let current = nums[i as usize] as int;
        
        if mid_val_opt.is_some() && current > mid_val_opt.unwrap() {
            return true;
        }
        
        if current > min_val {
            if mid_val_opt.is_none() || current < mid_val_opt.unwrap() {
                mid_val_opt = Some(current);
            }
        } else {
            min_val = current;
        }
        
        i += 1;
    }
    
    false
}
// </vc-code>

}
fn main() {}