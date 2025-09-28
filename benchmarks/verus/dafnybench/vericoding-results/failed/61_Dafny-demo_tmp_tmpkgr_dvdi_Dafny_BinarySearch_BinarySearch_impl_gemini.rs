// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(a: &[int], l: int, u: int) -> bool {
    forall|i: int, j: int| 0 <= l <= i <= j <= u < a.len() ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected forall syntax, removed unused parameters, and added proof. */
proof fn lemma_key_not_in_prefix(a: &[int], key: int, low: int, mid: int)
    requires
        sorted(a, 0, (a.len() - 1) as int),
        0 <= low <= mid < a.len(),
        a[mid] < key,
    ensures
        forall|k: int| low <= k <= mid ==> a[k] != key,
{
    forall|k: int| low <= k <= mid implies a[k] != key
    {
        assert(a[k] <= a[mid]); // from sorted
    }
}

/* helper modified by LLM (iteration 5): Corrected forall syntax, removed unused parameters, and added proof. */
proof fn lemma_key_not_in_suffix(a: &[int], key: int, mid: int, high: int)
    requires
        sorted(a, 0, (a.len() - 1) as int),
        0 <= mid <= high < a.len(),
        a[mid] > key,
    ensures
        forall|k: int| mid <= k <= high ==> a[k] != key,
{
    forall|k: int| mid <= k <= high implies a[k] != key
    {
        assert(a[mid] <= a[k]); // from sorted
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
/* code modified by LLM (iteration 5): Updated lemma calls to match modified helper signatures. */
{
    let mut low: i32 = 0;
    let mut high: i32 = (a.len() - 1) as i32;

    while low <= high
        invariant
            0 <= low,
            high < a.len() as i32,
            sorted(a, 0, (a.len() - 1) as int),
            forall|k: int| 0 <= k < a.len() as int && a[k] == key ==> low as int <= k <= high as int,
        decreases (high - low)
    {
        let mid = low + (high - low) / 2;
        if a[mid as usize] < key {
            proof {
                lemma_key_not_in_prefix(a, key, low as int, mid as int);
            }
            low = mid + 1;
        } else if a[mid as usize] > key {
            proof {
                lemma_key_not_in_suffix(a, key, mid as int, high as int);
            }
            high = mid - 1;
        } else {
            return mid;
        }
    }
    
    return -1;
}
// </vc-code>

}
fn main() {}