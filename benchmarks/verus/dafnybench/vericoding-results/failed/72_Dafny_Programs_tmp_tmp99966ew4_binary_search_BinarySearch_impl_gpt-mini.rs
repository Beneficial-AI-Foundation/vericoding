use vstd::prelude::*;

verus! {

spec fn sorted(a: &[int]) -> bool {
    forall|j: int, k: int| 0 <= j < k < a.len() ==> a[j] <= a[k]
}

// <vc-helpers>
// Helper lemmas moved into the implementation to avoid parsing/ordering issues.
// </vc-helpers>

// <vc-spec>
fn binary_search(a: &[int], value: int) -> (index: i32)
    requires 
        sorted(a),
    ensures 
        0 <= index ==> index < a.len() && a[index as int] == value,
        index < 0 ==> forall|k: int| 0 <= k < a.len() ==> a[k] != value,
// </vc-spec>
// <vc-code>
{
    let mut lo: int = 0;
    let mut hi: int = a.len() - 1;
    while lo <= hi
        invariant 0 <= lo && lo <= a.len()
        invariant -1 <= hi && hi < a.len()
        invariant forall|k: int| 0 <= k && k < a.len() ==> ((k < lo || k > hi) ==> a[k] != value)
    {
        let mid = lo + (hi - lo) / 2;
        // prove mid is between lo and hi to allow indexing
        {
            assert(0 <= hi - lo);
            assert((hi - lo) / 2 <= hi - lo);
            assert(lo <= lo + (hi - lo) / 2);
            assert(lo + (hi - lo) / 2 <= lo + (hi - lo));
            assert(lo + (hi - lo) / 2 <= hi);
        }
        assert(mid == lo + (hi - lo) / 2);
        assert(lo <= mid);
        assert(mid <= hi);
        assert(hi < a.len());
        assert(mid < a.len());
        let v = a[mid];
        if v == value {
            return mid as i32;
        } else if v < value {
            // prove forall k in [0..=mid]. a[k] < value
            assert(forall|k: int| 0 <= k && k <= mid ==> a[k] < value by {
                |k|
                if k == mid {
                    assert(a[k] == a[mid]);
                    assert(a[mid] < value);
                } else {
                    // k < mid
                    assert(0 <= k && k < mid && mid < a.len());
                    // from sorted(a) we get a[k] <= a[mid]
                    assert(a[k] <= a[mid]);
                    assert(a[mid] < value);
                    assert(a[k] < value);
                }
            });
            // establish the updated invariant for lo = mid + 1
            assert(forall|k: int| 0 <= k && k < a.len() ==> ((k < mid + 1 || k > hi) ==> a[k] != value) by {
                |k|
                if !(0 <= k && k < a.len()) {
                    assert((k < mid + 1 || k > hi) ==> a[k] != value);
                } else {
                    if k > hi {
                        // use old invariant
                        assert((k < lo || k > hi) ==> a[k] != value);
                        assert(a[k] != value);
                    } else {
                        // k <= hi
                        if k < mid + 1 {
                            // k <= mid
                            assert(0 <= k && k <= mid);
                            assert(a[k] < value);
                            assert(a[k] != value);
                        } else {
                            // mid+1 <= k <= hi, then (k < mid+1 || k > hi) is false
                            assert(!(k < mid + 1 || k > hi) ==> a[k] != value);
                        }
                    }
                    assert((k < mid + 1 || k > hi) ==> a[k] != value);
                }
            });
            lo = mid + 1;
        } else {
            // v > value
            // prove forall k in [mid..a.len()). a[k] > value
            assert(forall|k: int| mid <= k && k < a.len() ==> a[k] > value by {
                |k|
                if k == mid {
                    assert(a[k] == a[mid]);
                    assert(a[mid] > value);
                } else {
                    // mid < k
                    assert(mid < k && k < a.len());
                    // from sorted we get a[mid] <= a[k]
                    assert(a[mid] <= a[k]);
                    assert(a[mid] > value);
                    assert(a[k] > value);
                }
            });
            // establish the updated invariant for hi = mid - 1
            assert(forall|k: int| 0 <= k && k < a.len() ==> ((k < lo || k > mid - 1) ==> a[k] != value) by {
                |k|
                if !(0 <= k && k < a.len()) {
                    assert((k < lo || k > mid - 1) ==> a[k] != value);
                } else {
                    if k < lo {
                        // use old invariant
                        assert((k < lo || k > hi) ==> a[k] != value);
                        assert(a[k] != value);
                    } else {
                        // k >= lo
                        if k > mid - 1 {
                            // k >= mid
                            assert(mid <= k && k < a.len());
                            assert(a[k] > value);
                            assert(a[k] != value);
                        } else {
                            // lo <= k <= mid-1 => (k < lo || k > mid-1) is false
                            assert(!(k < lo || k > mid - 1) ==> a[k] != value);
                        }
                    }
                    assert((k < lo || k > mid - 1) ==> a[k] != value);
                }
            });
            hi = mid - 1;
        }
    }
    return -1 as i32;
}
// </vc-code>

fn main() {
}

}