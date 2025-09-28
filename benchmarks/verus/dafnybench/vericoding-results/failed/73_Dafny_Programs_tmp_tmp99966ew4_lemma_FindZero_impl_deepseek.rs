use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_monotonic(a: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] >= 0,
        forall|k: int| 0 < k < a.len() ==> a[k-1] - 1 <= a[k],
    ensures
        a[i] <= a[j] + (j - i)
{
    if i < j {
        lemma_monotonic(a, i, j-1);
        assert(a[j-1] - 1 <= a[j]);
        assert(a[i] <= a[j-1] + ((j-1) - i));
        assert(a[i] <= (a[j] + 1) + (j - i - 1));
        assert(a[i] <= a[j] + (j - i));
    }
}

proof fn lemma_no_zero_in_range(a: Seq<i32>, start: int, end: int)
    requires
        0 <= start <= end <= a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] >= 0,
        forall|k: int| 0 < k < a.len() ==> a[k-1] - 1 <= a[k],
        start < end ==> a[start] > (end - start) as i32,
    ensures
        forall|i: int| start <= i < end ==> a[i] != 0
{
    if start < end {
        lemma_monotonic(a, start, end-1);
        assert(a[start] <= a[end-1] + ((end-1) - start));
        assert(a[start] > (end - start) as i32);
        assert(a[end-1] > 0);
        
        let mut k: int = start;
        while k < end
            invariant
                start <= k <= end,
                forall|i: int| start <= i < k ==> a[i] != 0
            decreases end - k
        {
            if a[k] == 0 {
                assert(false);
            }
            k = k + 1;
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
    let mut left: i32 = 0;
    let mut right: i32 = (a.len() as i32) - 1;
    
    while left <= right
        invariant
            -1 <= left <= right + 1,
            right < a.len() as i32,
            forall|i: int| 0 <= i < left as int ==> a[i] != 0,
            forall|i: int| (right as int + 1) <= i < a.len() ==> a[i] != 0
        decreases (right - left) as int
    {
        let mid = left + (right - left) / 2;
        assert(left <= mid <= right);
        
        if a[mid as usize] == 0 {
            return mid;
        }
        
        proof {
            let a_seq = a.view();
            let mid_int = mid as int;
            let left_int = left as int;
            let right_int = right as int;
            
            if a_seq[mid_int] > (mid - left) as i32 {
                lemma_no_zero_in_range(a_seq, left_int, mid_int);
            }
            if a_seq[mid_int] > (right - mid) as i32 {
                lemma_no_zero_in_range(a_seq, mid_int + 1, right_int + 1);
            }
        }
        
        if a[mid as usize] > (mid - left) as i32 {
            left = mid + 1;
        } else {
            right = mid - 1;
        }
    }
    
    -1
}
// </vc-code>

fn main() {}

}