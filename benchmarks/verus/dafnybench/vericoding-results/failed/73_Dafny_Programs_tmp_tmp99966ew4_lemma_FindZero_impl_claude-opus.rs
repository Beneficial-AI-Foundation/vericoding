use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_no_zero_after(a: &[i32], k: int)
    requires
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a@[i] >= 0,
        forall|i: int| 0 < i < a.len() ==> #[trigger] a@[i-1] - 1 <= a@[i],
        0 <= k < a.len(),
        a@[k] > k,
    ensures
        forall|i: int| k <= i < a.len() ==> a@[i] != 0,
    decreases a.len() - k,
{
    if k < a.len() - 1 {
        assert(a@[k] - 1 <= a@[k + 1]);
        assert(a@[k + 1] >= a@[k] - 1 > k - 1 >= 0);
        assert(a@[k + 1] > 0);
        assert(a@[k + 1] >= k + 1);
        lemma_no_zero_after(a, k + 1);
    }
}

proof fn lemma_zero_exists_before(a: &[i32], k: int)
    requires
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a@[i] >= 0,
        forall|i: int| 0 < i < a.len() ==> #[trigger] a@[i-1] - 1 <= a@[i],
        0 <= k < a.len(),
        a@[k] < k,
    ensures
        exists|i: int| 0 <= i <= k && a@[i] == 0,
    decreases k + 1,
{
    if a@[k] == 0 {
        assert(a@[k] == 0);
    } else {
        assert(a@[k] > 0);
        if k == 0 {
            assert(a@[0] >= 0);
            assert(a@[0] < 0);
            assert(false);
        } else {
            assert(a@[k-1] - 1 <= a@[k]);
            assert(a@[k-1] <= a@[k] + 1 < k + 1);
            assert(a@[k-1] < k);
            lemma_zero_exists_before(a, k - 1);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn find_zero(a: &[i32]) -> (index: i32)
    requires
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] >= 0,
        forall|i: int| 0 < i < a.len() ==> #[trigger] a[i-1] - 1 <= a[i],
    ensures
        (index < 0 ==> forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] != 0),
        (0 <= index ==> index < a.len() && a[index as int] == 0),
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
            left <= a.len(),
            right < a.len(),
            forall|i: int| 0 <= i < left ==> a@[i] != 0,
            (exists|i: int| 0 <= i < a.len() && a@[i] == 0) ==> 
                exists|i: int| left <= i <= right && a@[i] == 0,
    {
        let mid = left + (right - left) / 2;
        
        if a[mid] == 0 {
            return mid as i32;
        } else if a[mid] > mid as i32 {
            proof {
                lemma_no_zero_after(a, mid as int);
            }
            if mid == 0 {
                return -1;
            }
            right = mid - 1;
        } else {
            assert(a[mid] < mid as i32);
            proof {
                lemma_zero_exists_before(a, mid as int);
            }
            left = mid + 1;
        }
    }
    
    -1
}
// </vc-code>

fn main() {}

}