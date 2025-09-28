use vstd::prelude::*;

verus! {

spec fn sorted(a: &[int]) -> bool {
    forall|j: int, k: int| 0 <= j < k < a.len() ==> a[j] <= a[k]
}

// <vc-helpers>
proof fn sorted_subrange(a: &[int], lo: int, hi: int)
    requires
        sorted(a),
        0 <= lo <= hi <= a.len(),
    ensures
        forall|j: int, k: int| lo <= j < k < hi ==> a[j] <= a[k],
{
}

proof fn sorted_implies_bounds(a: &[int], lo: int, hi: int, mid: int, value: int)
    requires
        sorted(a),
        0 <= lo <= mid < hi <= a.len(),
        a[mid] < value,
    ensures
        forall|k: int| lo <= k <= mid ==> a[k] < value,
{
    assert forall|k: int| lo <= k <= mid implies a[k] < value by {
        if lo <= k <= mid {
            assert(a[k] <= a[mid]);
            assert(a[mid] < value);
            assert(a[k] < value);
        }
    };
}

proof fn sorted_implies_upper_bounds(a: &[int], lo: int, hi: int, mid: int, value: int)
    requires
        sorted(a),
        0 <= lo <= mid < hi <= a.len(),
        a[mid] > value,
    ensures
        forall|k: int| mid <= k < hi ==> a[k] > value,
{
    assert forall|k: int| mid <= k < hi implies a[k] > value by {
        if mid <= k < hi {
            assert(a[mid] <= a[k]);
            assert(a[mid] > value);
            assert(a[k] > value);
        }
    };
}

proof fn value_not_in_array(a: &[int], value: int, lo: int, hi: int)
    requires
        0 <= lo,
        hi <= a.len(),
        lo >= hi,
        forall|k: int| 0 <= k < lo ==> a[k] < value,
        forall|k: int| hi <= k < a.len() ==> a[k] > value,
    ensures
        forall|k: int| 0 <= k < a.len() ==> a[k] != value,
{
    assert forall|k: int| 0 <= k < a.len() implies a[k] != value by {
        if 0 <= k < a.len() {
            if k < lo {
                assert(a[k] < value);
            } else if k >= hi {
                assert(a[k] > value);
            } else {
                assert(lo <= k < hi);
                assert(lo >= hi);
                assert(false);
            }
        }
    };
}
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
    let mut lo: usize = 0;
    let mut hi: usize = a.len();
    
    while lo < hi
        invariant
            0 <= lo <= hi <= a.len(),
            sorted(a),
            forall|k: int| 0 <= k < lo ==> a[k] < value,
            forall|k: int| hi <= k < a.len() ==> a[k] > value,
        decreases hi - lo,
    {
        let mid: usize = lo + (hi - lo) / 2;
        
        if a[mid] == value {
            assert(0 <= mid < a.len());
            assert(a[mid as int] == value);
            assert(mid <= i32::MAX as usize) by {
                assert(mid < a.len());
                assert(a.len() <= i32::MAX as usize);
            }
            return #[verifier::truncate] (mid as i32);
        } else if a[mid] < value {
            proof {
                sorted_implies_bounds(a, lo as int, hi as int, mid as int, value);
                assert(forall|k: int| lo as int <= k <= mid ==> a[k] < value);
            }
            lo = mid + 1;
        } else {
            proof {
                sorted_implies_upper_bounds(a, lo as int, hi as int, mid as int, value);
                assert(forall|k: int| mid <= k < hi as int ==> a[k] > value);
            }
            hi = mid;
        }
    }
    
    proof {
        value_not_in_array(a, value, lo as int, hi as int);
    }
    
    -1
}
// </vc-code>

fn main() {
}

}