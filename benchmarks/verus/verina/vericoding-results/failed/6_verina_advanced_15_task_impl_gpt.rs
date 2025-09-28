// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): remove nested proof block; straight-line proof via arithmetic */
proof fn trivial_le_trans(a: int, b: int, c: int)
    requires
        a <= b,
        b <= c,
    ensures
        a <= c
{
    assert(a <= c);
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
    /* code modified by LLM (iteration 4): exhaustive triple-loop with quantified invariants and explicit witnesses */
    let n: usize = nums.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            forall|ii: int, jj: int, kk: int|
                (0 <= ii && ii < (i as int) && ii < jj && jj < kk && kk < (n as int)) ==>
                    !(nums[ii] < nums[jj] && nums[jj] < nums[kk]),
        decreases n - i
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                j <= n,
                forall|jj: int, kk: int|
                    ((i as int) < jj && jj < (j as int) && jj < kk && kk < (n as int)) ==>
                        !(nums[i as int] < nums[jj] && nums[jj] < nums[kk]),
            decreases n - j
        {
            let mut k: usize = j + 1;
            while k < n
                invariant
                    k <= n,
                    forall|kk: int|
                        ((j as int) < kk && kk < (k as int)) ==>
                            !(nums[i as int] < nums[j as int] && nums[j as int] < nums[kk]),
                decreases n - k
            {
                if nums[i] < nums[j] && nums[j] < nums[k] {
                    proof {
                        let ii = i as int;
                        let jj = j as int;
                        let kk = k as int;
                        assert(0 <= ii && ii < jj && jj < kk && kk < (n as int));
                        assert(nums[ii] < nums[jj] && nums[jj] < nums[kk]);
                        assert(exists|iii: int, jjj: int, kkk: int|
                            0 <= iii && iii < jjj && jjj < kkk && kkk < (n as int) &&
                            nums[iii] < nums[jjj] && nums[jjj] < nums[kkk]);
                    }
                    return true;
                }
                proof {
                    assert(!(nums[i as int] < nums[j as int] && nums[j as int] < nums[k as int]));
                }
                k += 1;
            }
            proof {
                assert(forall|kk: int|
                    ((j as int) < kk && kk < (n as int)) ==>
                        !(nums[i as int] < nums[j as int] && nums[j as int] < nums[kk]));
            }
            j += 1;
        }
        proof {
            assert(forall|jj: int, kk: int|
                ((i as int) < jj && jj < kk && kk < (n as int)) ==>
                    !(nums[i as int] < nums[jj] && nums[jj] < nums[kk]));
        }
        i += 1;
    }
    proof {
        assert(forall|ii: int, jj: int, kk: int|
            (0 <= ii && ii < jj && jj < kk && kk < (n as int)) ==>
                !(nums[ii] < nums[jj] && nums[jj] < nums[kk]));
    }
    false
}
// </vc-code>

}
fn main() {}