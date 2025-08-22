use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn two_sum(nums: &Vec<i32>, target: i32) -> (ret: (usize, usize))
    requires
        nums.len() >= 2,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures
        /* code modified by LLM (iteration 2): fixed ensures clauses to use named return value */
        0 <= ret.0 < nums.len(),
        0 <= ret.1 < nums.len(),
        ret.0 != ret.1,
        nums[ret.0 as int] + nums[ret.1 as int] == target
{
    let mut i = 0;

    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            forall|u: int, v: int| 0 <= u < v < nums.len() && u < i ==> nums[u] + nums[v] != target,
            exists|u: int, v: int| i <= u < v < nums.len() && nums[u] + nums[v] == target,
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant
                0 <= i < j <= nums.len(),
                forall|u: int, v: int| 0 <= u < v < nums.len() && u < i ==> nums[u] + nums[v] != target,
                exists|u: int, v: int| i <= u < v < nums.len() && nums[u] + nums[v] == target,
                forall|u: int| i < u < j ==> nums[i as int] + nums[u] != target,
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    /* code modified by LLM (iteration 2): replaced unreachable code with proof of contradiction */
    proof {
        // At this point i == nums.len(), but we know from the precondition that
        // there exists a valid pair, which contradicts our loop invariant
        assert(false);
    }
    (0, 0) // This line will never be reached due to the proof above
}

fn main() {}
}