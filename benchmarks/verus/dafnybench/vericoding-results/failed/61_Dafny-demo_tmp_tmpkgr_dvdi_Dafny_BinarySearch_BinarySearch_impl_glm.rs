use vstd::prelude::*;

verus! {

// Predicate to check if array slice is sorted
spec fn sorted(a: &[int], l: int, u: int) -> bool {
    forall|i: int, j: int| 0 <= l <= i <= j <= u < a.len() ==> a[i] <= a[j]
}

// <vc-helpers>
proof fn sorted_implies_left_less(a: &[int], l: int, u: int, i: int, key: int)
    requires sorted(a, l, u),
    requires l <= i <= u,
    requires a[i] < key,
    ensures forall|j: int| l <= j <= i ==> a[j] < key
{
    assert forall|j: int| l <= j <= i implies a[j] <= a[i] by {
        assert(sorted(a, l, u));
    }
    assert forall|j: int| l <= j <= i implies a[j] < key by {
        assert(a[j] <= a[i]);
        assert(a[i] < key);
    }
}

proof fn sorted_implies_right_greater(a: &[int], l: int, u: int, i: int, key: int)
    requires sorted(a, l, u),
    requires l <= i <= u,
    requires key < a[i],
    ensures forall|j: int| i <= j <= u ==> key < a[j]
{
    assert forall|j: int| i <= j <= u implies a[i] <= a[j] by {
        assert(sorted(a, l, u));
    }
    assert forall|j: int| i <= j <= u implies key < a[j] by {
        assert(a[i] <= a[j]);
        assert(key < a[i]);
    }
}
// </vc-helpers>

// <vc-spec>
fn binary_search(a: &[int], key: int) -> (index: i32)
    requires 
        a.len() > 0,
        sorted(a, 0, (a.len() - 1) as int),
    ensures 
        index >= 0 ==> index < a.len() && a[index as int] == key,
        index < 0 ==> forall|k: int| 0 <= k < a.len() ==> a[k] != key,
// </vc-spec>
// <vc-code>
{
    let mut low: int = 0;
    let mut high: int = (a.len() - 1) as int;
    
    while low <= high
        invariant 0 <= low <= high + 1 <= a.len(),
        invariant forall|k: int| 0 <= k < low ==> a[k] < key,
        invariant forall|k: int| high < k < a.len() ==> key < a[k],
        decreases high - low + 1
    {
        let mid: int = low + (high - low) / 2;
        assert(0 <= mid < a.len());
        
        if a[mid] == key {
            return mid as i32;
        } else if a[mid] < key {
            low = mid + 1;
            proof {
                sorted_implies_left_less(a, 0, (a.len() - 1) as int, mid, key);
            }
        } else {
            high = mid - 1;
            proof {
                sorted_implies_right_greater(a, 0, (a.len() - 1) as int, mid, key);
            }
        }
    }
    
    assert forall|k: int| 0 <= k < a.len() implies a[k] != key by {
        if k < low {
            assert(a[k] < key);
        } else {
            assert(high < k);
            assert(key < a[k]);
        }
    };
    return -1;
}
// </vc-code>

fn main() {
}

}