use vstd::prelude::*;

verus! {

spec fn sorted(a: &[int]) -> bool {
    forall|j: int, k: int| 0 <= j < k < a.len() ==> a[j] <= a[k]
}

// <vc-helpers>
proof fn sorted_implies_monotonic(a: &[int], i: int, j: int)
    requires
        sorted(a),
        0 <= i <= j < a.len(),
    ensures
        a[i] <= a[j]
{
    if i == j {
        return;
    }
    assert(0 <= i < j < a.len());
    assert(forall|x: int, y: int| 0 <= x < y < a.len() ==> #[trigger] a[x] <= #[trigger] a[y]);
}

proof fn sorted_no_element_in_range(a: &[int], value: int, left: int, right: int)
    requires
        sorted(a),
        0 <= left < a.len(),
        0 <= right < a.len(),
        left <= right,
        a[left] > value || a[right] < value,
    ensures
        forall|k: int| left <= k <= right ==> a[k] != value
{
    if a[left] > value {
        assert(forall|k: int| left <= k <= right ==> a[left] <= a[k]) by {
            assert(forall|i: int, j: int| 0 <= i <= j < a.len() ==> #[trigger] a[i] <= #[trigger] a[j]);
        };
        assert(forall|k: int| left <= k <= right ==> #[trigger] a[k] >= a[left] > value);
    } else {
        assert(a[right] < value);
        assert(forall|k: int| left <= k <= right ==> a[k] <= a[right]) by {
            assert(forall|i: int, j: int| 0 <= i <= j < a.len() ==> #[trigger] a[i] <= #[trigger] a[j]);
        };
        assert(forall|k: int| left <= k <= right ==> #[trigger] a[k] <= a[right] < value);
    }
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
    if a.len() == 0 {
        return -1;
    }
    
    if a.len() > i32::MAX as usize {
        return -1;
    }
    
    let mut left: usize = 0;
    let mut right: usize = a.len() - 1;
    
    while left <= right
        invariant
            0 <= left <= a.len(),
            0 <= right < a.len(),
            a.len() <= i32::MAX as usize,
            sorted(a),
            forall|k: int| 0 <= k < left ==> #[trigger] a[k] < value,
            forall|k: int| right < k < a.len() ==> #[trigger] a[k] > value,
        decreases right as int - left as int
    {
        let mid = left + (right - left) / 2;
        
        if a[mid] == value {
            assert(0 <= mid < a.len());
            assert(a[mid as int] == value);
            assert(mid <= a.len() - 1);
            assert(a.len() <= i32::MAX as usize);
            assert(mid <= i32::MAX as usize);
            return mid as i32;
        } else if a[mid] < value {
            if mid == right {
                proof {
                    assert(forall|k: int| 0 <= k <= right ==> #[trigger] a[k] < value);
                    assert(forall|k: int| right < k < a.len() ==> #[trigger] a[k] > value);
                    assert(forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k] != value);
                }
                return -1;
            }
            left = mid + 1;
        } else {
            if mid == 0 {
                proof {
                    assert(a[0] > value);
                    sorted_no_element_in_range(a, value, 0, right as int);
                    assert(forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k] != value);
                }
                return -1;
            }
            right = mid - 1;
        }
    }
    
    proof {
        assert(left > right);
        assert(forall|k: int| 0 <= k < left ==> #[trigger] a[k] < value);
        assert(forall|k: int| right < k < a.len() ==> #[trigger] a[k] > value);
        if right >= 0 {
            assert(forall|k: int| 0 <= k <= right ==> #[trigger] a[k] < value);
        }
        if left < a.len() {
            assert(forall|k: int| left <= k < a.len() ==> #[trigger] a[k] > value);
        }
        assert(forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k] != value);
    }
    
    -1
}
// </vc-code>

fn main() {
}

}