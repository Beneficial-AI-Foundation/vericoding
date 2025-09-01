use vstd::prelude::*;

verus! {

// <vc-helpers>
// Empty - no additional helpers required
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
#[verifier::loop_isolation(false)]
fn two_sum(nums: &[i32], target: i32) -> (usize, usize) {
    let nums_seq = spec!{ nums@ };
    let n = spec!{ nums@.len() };
    assert(n == nums.len() as int);
    let mut i: usize = 0;
    while i < n as usize
        invariant
            0 <= i <= n,
            forall |k: int| 0 <= k < i ==> !exists |m: int|
                #[trigger] (k < m < n) &&
                #[trigger] (nums_seq[k] + nums_seq[m]) == target,
            exists |k: int, m: int|
                #[trigger] (i <= k < m < n) &&
                #[trigger] (nums_seq[k] + nums_seq[m]) == target
    {
        let mut j: usize = i + 1;
        while j < n as usize
            invariant
                i < j <= n,
                forall |m: int| #[trigger] (i < m < j) ==>
                    nums_seq[i] + nums_seq[m] != target
        {
            if spec!{ nums@[i as int] + nums@[j as int] == target } {
                return (i, j);
            }
            proof {
                assert(spec!{ nums@[i as int] + nums@[j as int] != target });
            }
            j = j + 1;
        }
        proof {
            assert(spec!{ forall |m: int| #[trigger] (i < m < n) ==>
                nums_seq[i] + nums_seq[m] != target });
            assert(spec!{ exists |k: int, m: int|
                #[trigger] ((i + 1) <= k < m < n) &&
                #[trigger] (nums_seq[k] + nums_seq[m]) == target });
        }
        i = i + 1;
    }
    proof {
        assert(spec!{ exists |k: int, m: int|
            #[trigger] (n <= k < m < n) &&
            #[trigger] (nums_seq[k] + nums_seq[m]) == target });
        assert(false);
    }
    (0, 0)
}
// </vc-code>

fn main() {}
}