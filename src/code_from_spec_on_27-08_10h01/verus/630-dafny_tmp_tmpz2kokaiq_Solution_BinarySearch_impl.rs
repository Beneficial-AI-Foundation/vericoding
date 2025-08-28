use vstd::prelude::*;

verus! {

spec fn sorted(a: &[int]) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

// <vc-helpers>
proof fn lemma_sorted_transitive(a: &[int], i: int, j: int, k: int)
    requires
        sorted(a),
        0 <= i <= j <= k < a.len(),
    ensures
        a[i] <= a[k],
{
    if i < k {
        if i < j && j < k {
            assert(a[i] <= a[j]);
            assert(a[j] <= a[k]);
        } else if i == j {
            assert(a[i] <= a[k]);
        } else if j == k {
            assert(a[i] <= a[k]);
        }
    }
}

proof fn lemma_binary_search_bounds(a: &[int], x: int, left: int, right: int, mid: int)
    requires
        sorted(a),
        0 <= left <= right < a.len(),
        left <= mid <= right,
        a[mid] < x,
    ensures
        forall|i: int| left <= i <= mid ==> a[i] != x,
{
    assert forall|i: int| left <= i <= mid implies a[i] != x by {
        if a[i] == x {
            lemma_sorted_transitive(a, i, mid, mid);
            assert(a[i] <= a[mid]);
            assert(a[mid] < x);
            assert(false);
        }
    }
}

proof fn lemma_binary_search_bounds_upper(a: &[int], x: int, left: int, right: int, mid: int)
    requires
        sorted(a),
        0 <= left <= right < a.len(),
        left <= mid <= right,
        x < a[mid],
    ensures
        forall|i: int| mid <= i <= right ==> a[i] != x,
{
    assert forall|i: int| mid <= i <= right implies a[i] != x by {
        if a[i] == x {
            lemma_sorted_transitive(a, mid, i, i);
            assert(a[mid] <= a[i]);
            assert(x < a[mid]);
            assert(false);
        }
    }
}

proof fn lemma_all_elements_checked(a: &[int], x: int, left: usize, right: usize)
    requires
        0 <= left as int,
        right as int < a@.len(),
        left > right,
        forall|i: int| 0 <= i < left as int ==> a[i] < x,
        forall|i: int| right as int < i < a@.len() ==> x < a[i],
    ensures
        forall|i: int| 0 <= i < a@.len() ==> a[i] != x,
{
    assert forall|i: int| 0 <= i < a@.len() implies a[i] != x by {
        if 0 <= i < left as int {
            assert(a[i] < x);
        } else if right as int < i < a@.len() {
            assert(x < a[i]);
        } else {
            assert(left as int <= i <= right as int);
            assert(left > right);
            assert(false);
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn binary_search(a: &[int], x: int) -> (index: i32)
    requires 
        sorted(a),
    ensures 
        0 <= index < a.len() ==> a[index as int] == x,
        index == -1 ==> forall|i: int| 0 <= i < a.len() ==> a[i] != x,
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if a.len() == 0 {
        return -1;
    }
    
    let mut left: usize = 0;
    let mut right: usize = a.len() - 1;
    
    while left <= right
        invariant
            0 <= left,
            right as int < a@.len(),
            forall|i: int| 0 <= i < left as int ==> a[i] < x,
            forall|i: int| right as int < i < a@.len() ==> x < a[i],
        decreases right as int - left as int + 1
    {
        let mid = left + (right - left) / 2;
        
        if a[mid] == x {
            proof {
                assert(0 <= mid as int < a@.len());
                assert(a[mid as int] == x);
            }
            return mid as i32;
        } else if a[mid] < x {
            proof {
                lemma_binary_search_bounds(a, x, left as int, right as int, mid as int);
            }
            if mid == usize::MAX {
                break;
            }
            left = mid + 1;
        } else {
            proof {
                lemma_binary_search_bounds_upper(a, x, left as int, right as int, mid as int);
            }
            if mid == 0 {
                break;
            }
            right = mid - 1;
        }
    }
    
    proof {
        lemma_all_elements_checked(a, x, left, right);
    }
    -1
}
// </vc-code>

fn main() {}

}