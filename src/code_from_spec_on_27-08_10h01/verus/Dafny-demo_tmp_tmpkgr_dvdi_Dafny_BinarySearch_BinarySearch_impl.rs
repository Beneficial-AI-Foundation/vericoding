use vstd::prelude::*;

verus! {

// Predicate to check if array slice is sorted
spec fn sorted(a: &[int], l: int, u: int) -> bool {
    forall|i: int, j: int| 0 <= l <= i <= j <= u < a.len() ==> a[i] <= a[j]
}

// <vc-helpers>
proof fn lemma_sorted_transitive(a: &[int], l: int, u: int, i: int, j: int, k: int)
    requires
        sorted(a, l, u),
        l <= i <= j <= k <= u,
        0 <= l,
        u < a.len(),
    ensures
        a[i] <= a[k]
{
}

proof fn lemma_sorted_subrange(a: &[int], l: int, u: int, l2: int, u2: int)
    requires
        sorted(a, l, u),
        l <= l2 <= u2 <= u,
        0 <= l,
        u < a.len(),
    ensures
        sorted(a, l2, u2)
{
}

proof fn lemma_array_len_bounds(a: &[int])
    requires
        a.len() > 0,
    ensures
        a.len() <= i32::MAX,
        (a.len() - 1) as i32 >= 0,
        (a.len() - 1) as i32 < a.len() as int,
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn binary_search(a: &[int], key: int) -> (index: i32)
    requires 
        a.len() > 0,
        sorted(a, 0, (a.len() - 1) as int),
    ensures 
        index >= 0 ==> index < a.len() && a[index as int] == key,
        index < 0 ==> forall|k: int| 0 <= k < a.len() ==> a[k] != key,
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    proof {
        lemma_array_len_bounds(a);
    }
    
    let mut low: i32 = 0;
    let mut high: i32 = #[verifier::truncate] (a.len() - 1) as i32;
    
    proof {
        assert(-1 <= high < a.len() as int);
        assert(forall|k: int| high < k < a.len() ==> a[k] > key) by {
            assert(high == (a.len() - 1) as i32);
            assert(high < a.len() - 1);
        }
    }
    
    while low <= high
        invariant
            0 <= low <= a.len(),
            -1 <= high < a.len() as int,
            sorted(a, 0, (a.len() - 1) as int),
            forall|k: int| 0 <= k < low ==> a[k] < key,
            forall|k: int| high < k < a.len() ==> a[k] > key,
        decreases high - low + 1
    {
        let mid = low + (high - low) / 2;
        
        proof {
            assert(low <= mid <= high);
            assert(0 <= mid < a.len());
            assert(mid < i32::MAX);
        }
        
        if a[mid as usize] == key {
            return mid;
        } else if a[mid as usize] < key {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    
    -1
}
// </vc-code>

fn main() {
}

}