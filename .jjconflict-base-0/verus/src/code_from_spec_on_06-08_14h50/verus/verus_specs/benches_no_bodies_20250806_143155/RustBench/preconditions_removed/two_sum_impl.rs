use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn two_sum(nums: &Vec<i32>, target: i32) -> (usize, usize)
    requires
        nums.len() >= 2,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures
        /* code modified by LLM (iteration 4): fixed ensures clause syntax to use proper result binding */
        (|result: (usize, usize)| {
            let (idx1, idx2) = result;
            0 <= idx1 < nums.len() &&
            0 <= idx2 < nums.len() &&
            idx1 != idx2 &&
            nums[idx1 as int] + nums[idx2 as int] == target
        })(result)
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
                forall|u: int| i + 1 <= u < j ==> nums[i as int] + nums[u] != target,
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    /* code modified by LLM (iteration 4): replaced unreachable!() with proof block and dummy return */
    proof {
        // We should never reach here because the precondition guarantees
        // that there exists a valid pair, and our loop should find it
        assert(false);
    }
    (0, 0) // This line should never be reached
}

fn main() {}
}