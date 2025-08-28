use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn solution_exists_at(nums: &[i32], target: i32, i: int, j: int) -> bool {
    0 <= i < j < nums.len() && nums[i] + nums[j] == target
}

spec fn solution_exists_from(nums: &[i32], target: i32, start_i: int) -> bool {
    exists|i: int, j: int| start_i <= i < j < nums.len() && nums[i] + nums[j] == target
}

spec fn solution_exists_from_j(nums: &[i32], target: i32, i: int, start_j: int) -> bool {
    exists|j: int| start_j <= j < nums.len() && j != i && nums[i] + nums[j] == target
}

spec fn no_solution_with_first(nums: &[i32], target: i32, first: int) -> bool {
    forall|j: int| first < j < nums.len() ==> nums[first] + nums[j] != target
}

spec fn no_solution_with_second(nums: &[i32], target: i32, second: int) -> bool {
    forall|i: int| 0 <= i < second ==> nums[i] + nums[second] != target
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_sum(nums: &[i32], target: i32) -> (result: (usize, usize))
    // pre-conditions-start
    requires
        nums.len() >= 2,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
        forall|i: int, j: int|
            0 <= i < nums.len() && 0 <= j < nums.len()
                ==> nums[i] + nums[j] <= i32::MAX
                    && nums[i] + nums[j] >= i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ({ let (i, j) = result; 0 <= i < nums.len() }),
        ({ let (i, j) = result; 0 <= j < nums.len() }),
        ({ let (i, j) = result; i != j }),
        ({ let (i, j) = result; nums[i as int] + nums[j as int] == target })
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut i: usize = 0;
    
    while i < nums.len()
        invariant
            i <= nums.len(),
            exists|x: int, y: int| 0 <= x < y < nums.len() && nums[x] + nums[y] == target,
            forall|x: int, y: int| 0 <= x < y < i ==> nums[x] + nums[y] != target,
        decreases nums.len() - i
    {
        let mut j: usize = i + 1;
        
        while j < nums.len()
            invariant
                i < nums.len(),
                j <= nums.len(),
                i + 1 <= j,
                exists|x: int, y: int| 0 <= x < y < nums.len() && nums[x] + nums[y] == target,
                forall|x: int, y: int| 0 <= x < y < i ==> nums[x] + nums[y] != target,
                forall|y: int| i < y < j ==> nums[i as int] + nums[y] != target,
            decreases nums.len() - j
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j += 1;
        }
        
        proof {
            assert(forall|y: int| i < y < nums.len() ==> nums[i as int] + nums[y] != target);
            assert(forall|x: int, y: int| 0 <= x < y < i ==> nums[x] + nums[y] != target);
            assert(forall|x: int, y: int| 0 <= x < y <= i ==> nums[x] + nums[y] != target) by {
                assert(forall|x: int| 0 <= x < i ==> nums[x] + nums[i as int] != target) by {
                    if exists|x: int| 0 <= x < i && nums[x] + nums[i as int] == target {
                        let x_wit = choose|x: int| 0 <= x < i && nums[x] + nums[i as int] == target;
                        assert(0 <= x_wit < i < nums.len());
                        assert(nums[x_wit] + nums[i as int] == target);
                        assert(false);
                    }
                }
            }
        }
        
        i += 1;
    }
    
    proof {
        assert(false);
    }
    (0, 0)
}
// </vc-code>

fn main() {}
}