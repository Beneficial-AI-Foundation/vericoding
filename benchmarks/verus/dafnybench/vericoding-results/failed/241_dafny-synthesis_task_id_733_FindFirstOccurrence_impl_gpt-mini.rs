use vstd::prelude::*;

verus! {

// <vc-helpers>
fn lemma_all_le_to_lt(arr: &[i32], target: i32, mid: int) -> ()
    requires 0 <= mid < arr.len()
    requires forall |i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
    requires arr[mid] < target
    ensures forall |i: int| 0 <= i <= mid ==> arr[i] < target
{
    proof {
        forall |i: int| (requires 0 <= i <= mid) {
            if i == mid {
                assert(arr[i] < target);
            } else {
                // i < mid, use monotonicity
                assert(0 <= i < mid);
                assert(arr[i] <= arr[mid]);
                assert(arr[i] < target);
            }
        }
    }
}

fn lemma_ge_from_ge(arr: &[i32], target: i32, mid: int) -> ()
    requires 0 <= mid < arr.len()
    requires forall |i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
    requires arr[mid] >= target
    ensures forall |i: int| mid <= i < arr.len() ==> arr[i] >= target
{
    proof {
        forall |i: int| (requires mid <= i < arr.len()) {
            if i == mid {
                assert(arr[i] >= target);
            } else {
                // mid < i, use monotonicity
                assert(mid < i < arr.len());
                assert(arr[mid] <= arr[i]);
                assert(arr[i] >= target);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn find_first_occurrence(arr: &[i32], target: i32) -> (result: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
    ensures
        (0 <= result < arr.len() ==> arr[result as int] == target) &&
        (result == -1 ==> forall|i: int| 0 <= i < arr.len() ==> arr[i] != target)
// </vc-spec>
// <vc-code>
{
    let n: int = arr.len();
    if n == 0 {
        return -1;
    }
    let mut lo: int = 0;
    let mut hi: int = n;
    while lo < hi
        invariant 0 <= lo <= hi <= n
        invariant forall |i: int| 0 <= i < lo ==> arr[i] < target
        invariant forall |i: int| hi <= i < n ==> arr[i] >= target
        decreases hi - lo
    {
        let mid: int = lo + (hi - lo) / 2;
        assert(0 <= mid && mid < n);
        if arr[mid] < target {
            // update lo to mid+1 and prove the invariants hold
            lemma_all_le_to_lt(arr, target, mid);
            lo = mid + 1;
        } else {
            // arr[mid] >= target, update hi to mid and prove right-side invariant
            lemma_ge_from_ge(arr, target, mid);
            hi = mid;
        }
    }
    // now lo == hi is the first index with arr[index] >= target (or n)
    if lo < n && arr[lo] == target {
        return lo as i32;
    } else {
        // prove there is no element equal to target
        proof {
            if lo >= n {
                forall |i: int| (requires 0 <= i < n) {
                    // since i < n <= lo, i < lo, so left invariant gives arr[i] < target
                    assert(0 <= i < lo);
                    assert(arr[i] < target);
                    assert(arr[i] != target);
                }
            } else {
                // lo < n and arr[lo] != target
                // from right invariant we have arr[lo] >= target
                assert(arr[lo] >= target);
                assert(arr[lo] != target);
                // hence arr[lo] > target
                assert(arr[lo] > target);
                // for i < lo: arr[i] < target (left invariant)
                assert(forall |i: int| 0 <= i < lo ==> arr[i] < target);
                forall |i: int| (requires lo <= i < n) {
                    if i == lo {
                        assert(arr[i] > target);
                    } else {
                        assert(lo < i < n);
                        assert(arr[lo] <= arr[i]);
                        assert(arr[i] > target);
                    }
                }
                forall |i: int| (requires 0 <= i < n) {
                    if i < lo {
                        assert(arr[i] < target);
                        assert(arr[i] != target);
                    } else {
                        // lo <= i < n
                        assert(arr[i] > target);
                        assert(arr[i] != target);
                    }
                }
            }
        }
        return -1;
    }
}
// </vc-code>

fn main() {
}

}