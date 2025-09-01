use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn barrier(arr: &[i32], p: usize) -> (result: bool)
    // pre-conditions-start
    requires
        arr.len() > 0,
        0 <= p < arr.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == forall|k: int, l: int| 0 <= k <= p && p < l < arr.len() ==> arr[k] < arr[l],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = arr.len();
    let mut res: bool = true;
    let mut k: usize = 0;
    while k <= p {
        invariant k <= p + 1usize;
        invariant res == forall|kk: int, ll: int| #[trigger] 0 <= kk && kk < k as int && kk <= p as int && p as int < ll && ll < n as int ==> arr[kk as usize] < arr[ll as usize];
        let mut l: usize = p + 1;
        while l < n {
            invariant p + 1usize <= l && l <= n;
            invariant res ==
                (forall|kk: int, ll: int| #[trigger] 0 <= kk && kk < k as int && kk <= p as int && p as int < ll && ll < n as int ==> arr[kk as usize] < arr[ll as usize])
                &&
                (forall|ll2: int| #[trigger] p as int < ll2 && ll2 < l as int ==> arr[k as usize] < arr[ll2 as usize]);
            if !(arr[k] < arr[l]) {
                // we found a counterexample, prove the postcondition by exhibiting witnesses and return false
                proof {
                    // Witnesses are kk = k as int, ll = l as int
                    assert(0 <= k as int);
                    assert(k as int <= p as int);
                    assert(p as int < l as int);
                    assert(l as int < n as int);
                    assert(!(arr[k] < arr[l]));
                    assert(exists|kk: int, ll: int| 0 <= kk && kk <= p as int && p as int < ll && ll < n as int && !(arr[kk as usize] < arr[ll as usize]));
                    // provide the concrete witness
                    assert(exists|kk: int, ll: int| kk == k as int && ll == l as int && 0 <= kk && kk <= p as int && p as int < ll && ll < n as int && !(arr[kk as usize] < arr[ll as usize]));
                }
                return false;
            }
            l += 1;
        }
        k += 1;
    }
    // At loop exit, k == p + 1 and the invariant gives the desired universal property
    proof {
        assert(k == p + 1usize);
        assert(res == forall|kk: int, ll: int| #[trigger] 0 <= kk && kk < k as int && kk <= p as int && p as int < ll && ll < n as int ==> arr[kk as usize] < arr[ll as usize]);
        // since k == p+1, kk < k is equivalent to kk <= p, so we have the required form
        assert(res == forall|kk: int, ll: int| #[trigger] 0 <= kk && kk <= p as int && p as int < ll && ll < n as int ==> arr[kk as usize] < arr[ll as usize]);
    }
    res
}
// </vc-code>

fn main() {}
}