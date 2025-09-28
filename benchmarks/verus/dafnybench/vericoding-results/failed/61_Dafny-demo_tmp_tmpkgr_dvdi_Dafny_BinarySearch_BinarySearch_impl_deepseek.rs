use vstd::prelude::*;

verus! {

// Predicate to check if array slice is sorted
spec fn sorted(a: &[int], l: int, u: int) -> bool {
    forall|i: int, j: int| 0 <= l <= i <= j <= u < a.len() ==> a[i] <= a[j]
}

// <vc-helpers>
spec fn sorted(a: &[int], l: int, u: int) -> bool {
    forall|i: int, j: int| l <= i <= j <= u < a.len() as int ==> a[i] <= a[j]
}

proof fn lemma_sorted_slice(a: &[int], l: int, u: int, i: int, j: int)
    requires
        sorted(a, l, u),
        l <= i <= j <= u,
    ensures
        a[i] <= a[j]
{
}

proof fn lemma_sorted_subrange(a: &[int], l: int, m: int, u: int)
    requires
        sorted(a, l, u),
        l <= m <= u,
    ensures
        sorted(a, l, m),
        sorted(a, m, u)
{
}

proof fn lemma_sorted_index_bounds(a: &[int], l: int, u: int, i: int)
    requires
        sorted(a, l, u),
        l <= i <= u,
    ensures
        a[l] <= a[i] <= a[u]
{
}

spec fn contains(a: &[int], key: int, l: int, u: int) -> bool {
    exists|i: int| l <= i <= u && a[i] == key
}

proof fn lemma_sorted_transitive(a: &[int], i: int, j: int, k: int)
    requires
        sorted(a, 0, (a.len() - 1) as int),
        0 <= i <= j <= k < a.len() as int,
    ensures
        a[i] <= a[k]
{
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
    let mut low: usize = 0;
    let mut high: usize = a.len() - 1;
    
    while low <= high
        invariant
            low <= high < a.len(),
            forall|k: int| 0 <= k < a.len() as int && !(low as int <= k <= high as int) ==> a[k] != key,
            sorted(a, 0, (a.len() - 1) as int),
        decreases (high - low)
    {
        let mid = low + (high - low) / 2;
        
        if a[mid] == key {
            return mid as i32;
        } else if a[mid] < key {
            proof {
                lemma_sorted_index_bounds(a, 0, (a.len() - 1) as int, mid as int);
                assert forall|k: int| 0 <= k <= mid as int implies a[k] <= a[mid] by {
                    lemma_sorted_index_bounds(a, 0, mid as int, k);
                };
                assert forall|k: int| 0 <= k <= mid as int implies (a[k] <= a[mid] && a[mid] < key) ==> a[k] != key by {
                    if 0 <= k <= mid as int {
                        lemma_sorted_index_bounds(a, 0, mid as int, k);
                        assert(a[k] <= a[mid]);
                        if a[mid] < key {
                            assert(a[k] < key);
                        }
                    }
                };
            }
            low = mid + 1;
        } else {
            proof {
                lemma_sorted_index_bounds(a, 0, (a.len() - 1) as int, mid as int);
                assert forall|k: int| mid as int <= k < a.len() as int implies a[mid] <= a[k] by {
                    if mid as int <= k < a.len() as int {
                        lemma_sorted_index_bounds(a, mid as int, (a.len() - 1) as int, k);
                    }
                };
                assert forall|k: int| mid as int <= k < a.len() as int implies (key < a[mid] && a[mid] <= a[k]) ==> a[k] != key by {
                    if mid as int <= k < a.len() as int {
                        lemma_sorted_index_bounds(a, mid as int, (a.len() - 1) as int, k);
                        assert(a[mid] <= a[k]);
                        if key < a[mid] {
                            assert(key < a[k]);
                        }
                    }
                };
            }
            if mid == 0 {
                break;
            }
            high = mid - 1;
        }
    }
    
    -1
}
// </vc-code>

fn main() {
}

}