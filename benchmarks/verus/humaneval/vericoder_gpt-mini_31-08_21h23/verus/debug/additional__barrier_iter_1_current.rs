use vstd::prelude::*;

verus! {

// <vc-helpers>

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
        invariant k <= p + 1;
        invariant res == forall|kk: int, ll: int| #[trigger] 0 <= kk && kk < k as int && kk <= p as int && p as int < ll && ll < n as int ==> arr[kk as usize] < arr[ll as usize];
        let mut l: usize = p + 1;
        while l < n {
            invariant p + 1 <= l && l <= n;
            invariant res ==
                (forall|kk: int, ll: int| #[trigger] 0 <= kk && kk < k as int && kk <= p as int && p as int < ll && ll < n as int ==> arr[kk as usize] < arr[ll as usize])
                &&
                (forall|ll2: int| #[trigger] p as int < ll2 && ll2 < l as int ==> arr[k as usize] < arr[ll2 as usize]);
            if !(arr[k] < arr[l]) {
                res = false;
            }
            l += 1;
        }
        k += 1;
    }
    res
}
// </vc-code>

fn main() {}
}