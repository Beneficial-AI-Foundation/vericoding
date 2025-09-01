use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let n_usize = nums.len();
    let n = n_usize as int;

    let ghost pair = choose|p: (int, int)|
        0 <= p.0 < p.1 < n && nums[p.0] + nums[p.1] == target;
    let ghost iw: int = pair.0;
    let ghost jw: int = pair.1;

    assert(0 <= iw && iw < jw && jw < n);

    let mut found: bool = false;
    let mut ri: usize = 0;
    let mut rj: usize = 1;

    let mut i: usize = 0;
    while i < n_usize
        invariant 0 <= i <= n_usize
        invariant found ==> ({
            let ii = ri as int;
            let jj = rj as int;
            0 <= ii < jj < n && nums[ii] + nums[jj] == target
        })
        invariant !found ==> (i as int) <= iw
        decreases n_usize - i
    {
        let mut j: usize = i + 1;
        while j < n_usize
            invariant 0 <= i < n_usize
            invariant i + 1 <= j <= n_usize
            invariant found ==> ({
                let ii = ri as int;
                let jj = rj as int;
                0 <= ii < jj < n && nums[ii] + nums[jj] == target
            })
            invariant !found ==> (
                (i as int) < iw
                ||
                ((i as int) == iw && (j as int) <= jw)
            )
            decreases n_usize - j
        {
            assert(0 <= i as int && (i as int) < n);
            assert(0 <= j as int && (j as int) < n);
            assert(
                nums[i as int] + nums[j as int] <= i32::MAX
                &&
                nums[i as int] + nums[j as int] >= i32::MIN
            );

            if nums[i] == target - nums[j] {
                // Using subtraction might also require bounds; use addition instead:
            }

            if nums[i] + nums[j] == target {
                found = true;
                ri = i;
                rj = j;
                // found invariant holds
                break;
            }

            // Maintain the not-passed-witness invariant
            proof {
                if !found {
                    // From the invariant, either i < iw or (i == iw && j <= jw)
                    // Since we just checked (i, j) and did not find the target,
                    // it cannot be that (i, j) = (iw, jw). Therefore,
                    // if i == iw then j < jw, hence after increment j' = j + 1 we have j' <= jw.
                }
            }

            j += 1;
        }

        if found {
            // Outer invariants already satisfied by found clause
            break;
        }

        // If inner loop finished without finding, then j == n_usize.
        // From the inner invariant !found ==> (i < iw) || (i == iw && j <= jw).
        // Since j == n_usize and jw < n, it cannot be that i == iw.
        // Hence i < iw, so after increment we maintain i <= iw.
        if j == n_usize {
            assert(!found);
            assert((i as int) < iw);
        }

        i += 1;
    }

    // Must have found due to existence of witness and traversal of all pairs
    assert(found);
    assert({
        let ii = ri as int;
        let jj = rj as int;
        0 <= ii < jj < n
    });
    assert(
        nums[ri as int] + nums[rj as int] <= i32::MAX
        &&
        nums[ri as int] + nums[rj as int] >= i32::MIN
    );
    assert(nums[ri as int] + nums[rj as int] == target);

    (ri, rj)
}
// </vc-code>

fn main() {}
}