use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn sum_in_bounds(nums: &[i32], i: int, j: int)
    requires
        0 <= i < nums.len(),
        0 <= j < nums.len(),
        forall|a: int, b: int|
            0 <= a < nums.len() && 0 <= b < nums.len()
                ==> nums[a] + nums[b] <= i32::MAX
                    && nums[a] + nums[b] >= i32::MIN,
    ensures
        nums[i] + nums[j] <= i32::MAX
            && nums[i] + nums[j] >= i32::MIN,
{
    assert(forall|a: int, b: int|
        0 <= a < nums.len() && 0 <= b < nums.len()
            ==> nums[a] + nums[b] <= i32::MAX
                && nums[a] + nums[b] >= i32::MIN);
    assert(0 <= i && i < nums.len());
    assert(0 <= j && j < nums.len());
    assert(nums[i] + nums[j] <= i32::MAX);
    assert(nums[i] + nums[j] >= i32::MIN);
}

open spec fn is_solution(nums: &[i32], n: int, i: usize, j: usize, target: i32) -> bool {
    let ii = i as int;
    let jj = j as int;
    0 <= ii && ii < jj && jj < n && nums[ii] + nums[jj] == target
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
        invariant 0 <= (i as int) && (i as int) <= n
        invariant found ==> is_solution(nums, n, ri, rj, target)
        invariant !found ==> (i as int) <= iw
        decreases (n_usize - i) as int
    {
        let mut j: usize = i + 1;
        while j < n_usize
            invariant 0 <= (i as int) && (i as int) < n
            invariant (i as int) + 1 <= (j as int) && (j as int) <= n
            invariant found ==> is_solution(nums, n, ri, rj, target)
            invariant !found ==> (
                (i as int) < iw
                ||
                ((i as int) == iw && (j as int) <= jw)
            )
            decreases (n_usize - j) as int
        {
            assert(0 <= i as int && (i as int) < n);
            assert(0 <= j as int && (j as int) < n);

            proof { sum_in_bounds(nums, i as int, j as int); }

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
                proof {
                    if !found {
                        assert((i as int) < iw || ((i as int) == iw && (j as int) <= jw));
                        if (i as int) == iw {
                            assert(nums[i as int] + nums[j as int] != target);
                            assert(nums[iw] + nums[jw] == target);
                            assert((j as int) != jw);
                            assert((j as int) <= jw);
                            assert((j as int) < jw);
                            assert(((j + 1) as int) == (j as int) + 1);
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

        assert(j >= n_usize);
        assert(j <= n_usize);
        assert(j == n_usize);

        assert(!found);
        proof {
            assert((i as int) < iw || ((i as int) == iw && (j as int) <= jw));
            assert((j as int) == n);
            assert(jw < n);
            assert(!((j as int) <= jw));
            assert((i as int) < iw);
        }

        let i_old = i;
        assert(i_old < n_usize);
        i += 1;
        assert(((i as int) == (i_old as int) + 1));
        assert((i as int) <= iw);
    }

    proof {
        if !found {
            assert(!(i < n_usize));
            assert(i >= n_usize);
            assert(i <= n_usize);
            assert(i == n_usize);
            assert((i as int) == n);
            assert((i as int) <= iw);
            assert(!(n <= iw));
            assert(false);
        }
    }
    assert(found);
    assert(is_solution(nums, n, ri, rj, target));
    assert(nums[ri as int] + nums[rj as int] == target);

    (ri, rj)
}
// </vc-code>

fn main() {}
}