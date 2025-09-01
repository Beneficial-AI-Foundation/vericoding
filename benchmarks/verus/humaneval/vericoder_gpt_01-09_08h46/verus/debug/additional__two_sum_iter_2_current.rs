use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
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

    let ghost pair = choose|p: (int, int)| 0 <= p.0 < p.1 < n && nums[p.0] + nums[p.1] == target;
    let ghost iw: int = pair.0;
    let ghost jw: int = pair.1;

    assert(0 <= iw && iw < jw && jw < n);

    let mut found: bool = false;
    let mut ri: usize = 0;
    let mut rj: usize = 1;

    let mut i: usize = 0;
    while i < n_usize
        invariant 0 <= i <= n_usize
        invariant found ==> {
            let ii = ri as int;
            let jj = rj as int;
            0 <= ii < jj < n && nums[ii] + nums[jj] == target
        }
        invariant !found ==> (i as int) <= iw
        decreases (n_usize - i) as int
    {
        let mut j: usize = i + 1;
        while j < n_usize
            invariant 0 <= i < n_usize
            invariant i + 1 <= j <= n_usize
            invariant found ==> {
                let ii = ri as int;
                let jj = rj as int;
                0 <= ii < jj < n && nums[ii] + nums[jj] == target
            }
            invariant !found ==> (
                (i as int) < iw
                ||
                ((i as int) == iw && (j as int) <= jw)
            )
            decreases (n_usize - j) as int
        {
            assert(0 <= i as int && (i as int) < n);
            assert(0 <= j as int && (j as int) < n);
            assert(
                nums[i as int] + nums[j as int] <= i32::MAX
                &&
                nums[i as int] + nums[j as int] >= i32::MIN
            );

            if nums[i] + nums[j] == target {
                found = true;
                ri = i;
                rj = j;
                proof {
                    let ii = ri as int;
                    let jj = rj as int;
                    assert(0 <= ii && ii < jj && jj < n);
                    assert(nums[ii] + nums[jj] == target);
                }
                break;
            } else {
                // Maintain the not-passed-witness invariant across j += 1
                proof {
                    if !found {
                        assert((i as int) < iw || ((i as int) == iw && (j as int) <= jw));
                        if (i as int) == iw {
                            // Since we are in the else branch, this pair does not sum to target
                            assert(nums[i as int] + nums[j as int] != target);
                            // The witness pair (iw, jw) does sum to target
                            assert(nums[iw] + nums[jw] == target);
                            // Hence if j == jw we would have found the target; contradiction
                            assert((j as int) != jw);
                            // From j <= jw and j != jw we get j < jw
                            assert((j as int) < jw);
                            // Therefore after increment we still have j' <= jw
                            assert(((j + 1) as int) <= jw);
                        }
                    }
                }
            }

            j += 1;
        }

        if found {
            break;
        }

        // If inner loop finished without finding, then j == n_usize
        assert(j >= n_usize);
        assert(j <= n_usize);
        assert(j == n_usize);

        // From inner invariant and j == n_usize > jw, deduce i < iw
        assert(!found);
        proof {
            // !found ==> (i < iw) || (i == iw && j <= jw)
            assert((i as int) < iw || ((i as int) == iw && (j as int) <= jw));
            // But j == n_usize ==> j as int == n
            assert((j as int) == n);
            // jw < n
            assert(jw < n);
            // So (j as int) <= jw is impossible
            assert(!((j as int) <= jw));
            // Therefore i < iw
            assert((i as int) < iw);
        }

        let i_old = i;
        i += 1;
        // Maintain outer invariant !found ==> i <= iw
        assert((i_old as int) < iw);
        assert((i as int) == (i_old as int) + 1);
        assert((i as int) <= iw);
    }

    // Must have found due to existence of witness and traversal of all pairs
    proof {
        if !found {
            assert(!(i < n_usize)); // loop condition false
            assert(i >= n_usize);
            assert(i <= n_usize);
            assert(i == n_usize);
            assert((i as int) == n);
            assert((i as int) <= iw); // from outer invariant
            assert(!(n <= iw)); // since iw < n
            assert(false);
        }
    }
    assert(found);
    assert({
        let ii = ri as int;
        let jj = rj as int;
        0 <= ii && ii < jj && jj < n
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