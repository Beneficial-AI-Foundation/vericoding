// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): simple integer min function */
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_sum(nums: &[i32], target: i32) -> (result: (usize, usize))
    requires
        nums.len() >= 2,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
        forall|i: int, j: int|
            0 <= i < nums.len() && 0 <= j < nums.len()
                ==> nums[i] + nums[j] <= i32::MAX
                    && nums[i] + nums[j] >= i32::MIN,
    ensures
        ({ let (i, j) = result; 0 <= i < nums.len() }),
        ({ let (i, j) = result; 0 <= j < nums.len() }),
        ({ let (i, j) = result; i != j }),
        ({ let (i, j) = result; nums[i as int] + nums[j as int] == target })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): nested loops with preserved invariants and proof after inner loop, fixed choose syntax */
    let n = nums.len();
    let mut i: usize = 0;
    while i + 1 < n
        invariant
            i < n,
            exists|a: int, b: int|
                (i as int) <= a && a < b && b < (n as int) && nums[a as int] + nums[b as int] == target,
        decreases n - i
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                i < n,
                (j as int) <= (n as int),
                (i as int) + 1 <= (j as int),
                exists|a: int, b: int|
                    (i as int) <= a && a < b && b < (n as int) && nums[a as int] + nums[b as int] == target,
                forall|k: int|
                    (i as int) + 1 <= k && k < (j as int) ==> nums[i as int] + nums[k as int] != target,
            decreases n - j
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j += 1;
        }
        proof {
            assert((j as int) == (n as int));
            let (a, b) = choose|a: int, b: int| (i as int) <= a && a < b && b < (n as int) && nums[a as int] + nums[b as int] == target;
            if a == i as int {
                assert((i as int) + 1 <= b);
                assert(forall|k: int| (i as int) + 1 <= k && k < (n as int) ==> nums[i as int] + nums[k as int] != target);
                assert(nums[i as int] + nums[b as int] != target);
                assert(nums[a as int] + nums[b as int] == target);
                assert(false);
            }
            assert((i as int) + 1 <= a);
            assert(exists|x: int, y: int| ((i as int) + 1 <= x && x < y && y < (n as int) && nums[x as int] + nums[y as int] == target));
        }
        i += 1;
    }
    (0usize, 0usize)
}
// </vc-code>

}
fn main() {}